/*
 * Copyright Cedar Contributors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *      https://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#![no_main]

use cedar_drt::logger::initialize_log;
use cedar_drt_inner::fuzz_target;

use cedar_policy::{
    AuthorizationError, Authorizer, Entities, EvaluationError, Policy, PolicySet, Request, Schema,
    ValidationMode, Validator,
};

use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema,
    settings::ABACSettings,
};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, schema, and 8 associated policies
#[derive(Debug, Clone)]
struct FuzzTargetInput {
    /// generated schema
    pub schema: schema::Schema,
    /// generated hierarchy
    pub hierarchy: Hierarchy,
    /// the policy which we will see if it validates
    pub policy: ABACPolicy,
    /// the requests to try, if the policy validates.
    /// We try 8 requests per validated policy.
    pub requests: [ABACRequest; 8],
}

/// settings for this fuzz target
const SETTINGS: ABACSettings = ABACSettings {
    match_types: true,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
    per_action_request_env_limit: ABACSettings::default_per_action_request_env_limit(),
    total_action_request_env_limit: ABACSettings::default_total_action_request_env_limit(),
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: schema::Schema = schema::Schema::arbitrary(SETTINGS.clone(), u)?;
        let hierarchy = schema.arbitrary_hierarchy(u)?;
        let policy = schema.arbitrary_policy(&hierarchy, u)?;
        let requests = [
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
            schema.arbitrary_request(&hierarchy, u)?,
        ];
        Ok(Self {
            schema,
            hierarchy,
            policy,
            requests,
        })
    }

    fn try_size_hint(
        depth: usize,
    ) -> arbitrary::Result<(usize, Option<usize>), arbitrary::MaxRecursionReached> {
        Ok(arbitrary::size_hint::and_all(&[
            schema::Schema::arbitrary_size_hint(depth)?,
            HierarchyGenerator::size_hint(depth),
            schema::Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
            schema::Schema::arbitrary_request_size_hint(depth),
        ]))
    }
}

/// helper function that just tells us whether a policyset passes validation
fn passes_validation(validator: &Validator, policyset: &PolicySet, mode: ValidationMode) -> bool {
    validator.validate(policyset, mode).validation_passed()
}

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.schema.schemafile_string();
    if let Ok(schema) = Schema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        if let Ok(entities) = Entities::try_from(input.hierarchy.clone()) {
            let validator = Validator::new(schema);
            let mut policyset = PolicySet::new();
            let policy: Policy = input.policy.into();
            policyset.add(policy.clone()).unwrap();
            let passes_strict = passes_validation(&validator, &policyset, ValidationMode::Strict);
            let passes_permissive =
                passes_validation(&validator, &policyset, ValidationMode::Permissive);
            if passes_permissive {
                // policy successfully validated, let's make sure we don't get any
                // dynamic type errors
                let authorizer = Authorizer::new();
                debug!("Policies: {policyset}");
                debug!("Entities: {}", entities.as_ref());
                for r in input.requests.into_iter() {
                    let q = Request::from(r);
                    debug!("Request: {q}");
                    let ans = authorizer.is_authorized(&q, &policyset, &entities);

                    let unexpected_errs = ans
                        .diagnostics()
                        .errors()
                        .filter_map(|error| match error {
                            AuthorizationError::PolicyEvaluationError(err) => {
                                match err.inner() {
                                    // Evaluation errors the validator should prevent.
                                    EvaluationError::RecordAttrDoesNotExist(_)
                                    | EvaluationError::EntityAttrDoesNotExist(_)
                                    | EvaluationError::FailedExtensionFunctionLookup(_)
                                    | EvaluationError::TypeError(_)
                                    | EvaluationError::WrongNumArguments(_) => {
                                        Some(error.to_string())
                                    }
                                    // Evaluation errors it shouldn't prevent. Not
                                    // written with a catch all so that we must
                                    // consider if a new error type should cause
                                    // this target to fail.
                                    EvaluationError::EntityDoesNotExist(_)
                                    | EvaluationError::IntegerOverflow(_)
                                    | EvaluationError::UnlinkedSlot(_)
                                    | EvaluationError::FailedExtensionFunctionExecution(_)
                                    | EvaluationError::NonValue(_)
                                    | EvaluationError::RecursionLimit(_) => None,
                                }
                            }
                        })
                        .collect::<Vec<_>>();

                    assert_eq!(
                        unexpected_errs,
                        Vec::<String>::new(),
                        "validated policy produced unexpected errors {unexpected_errs:?}!\npolicies:\n{policyset}\nentities:\n{}\nschema:\n{schemafile_string}\nrequest:\n{q}\n",
                        entities.as_ref()
                    )
                }
            } else {
                assert!(
                    !passes_strict,
                    "policy fails permissive validation but passes strict validation!\npolicies:\n{policyset}\nentities:\n{}\nschema:\n{schemafile_string}\n",
                    entities.as_ref()
                );
            }
        }
    }
});
