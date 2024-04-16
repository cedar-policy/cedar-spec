/*
 * Copyright Cedar Contributors. All Rights Reserved.
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
use cedar_drt::initialize_log;
use cedar_drt_inner::*;
use cedar_policy_core::ast;
use cedar_policy_core::authorizer::{AuthorizationError, Authorizer};
use cedar_policy_core::entities::Entities;
use cedar_policy_core::evaluator::EvaluationErrorKind;
use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema::Schema,
    settings::ABACSettings,
};
use cedar_policy_validator::{ValidationMode, Validator, ValidatorSchema};
use libfuzzer_sys::arbitrary::{self, Arbitrary, Unstructured};
use log::debug;
use serde::Serialize;
use std::convert::TryFrom;

/// Input expected by this fuzz target:
/// An ABAC hierarchy, schema, and 8 associated policies
#[derive(Debug, Clone, Serialize)]
struct FuzzTargetInput {
    /// generated schema
    #[serde(skip)]
    pub schema: Schema,
    /// generated hierarchy
    #[serde(skip)]
    pub hierarchy: Hierarchy,
    /// the policy which we will see if it validates
    pub policy: ABACPolicy,
    /// the requests to try, if the policy validates.
    /// We try 8 requests per validated policy.
    #[serde(skip)]
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
    enable_unspecified_apply_spec: true,
};

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        let schema: Schema = Schema::arbitrary(SETTINGS.clone(), u)?;
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

    fn size_hint(depth: usize) -> (usize, Option<usize>) {
        arbitrary::size_hint::and_all(&[
            Schema::arbitrary_size_hint(depth),
            HierarchyGenerator::size_hint(depth),
            Schema::arbitrary_policy_size_hint(&SETTINGS, depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
            Schema::arbitrary_request_size_hint(depth),
        ])
    }
}

/// helper function that just tells us whether a policyset passes validation
fn passes_validation(validator: &Validator, policyset: &ast::PolicySet) -> bool {
    validator
        .validate(policyset, ValidationMode::default())
        .validation_passed()
}

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput| {
    initialize_log();
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.schema.schemafile_string();
    if let Ok(schema) = ValidatorSchema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        if let Ok(entities) = Entities::try_from(input.hierarchy.clone()) {
            let validator = Validator::new(schema);
            let mut policyset = ast::PolicySet::new();
            let policy: ast::StaticPolicy = input.policy.into();
            policyset.add_static(policy.clone()).unwrap();
            if passes_validation(&validator, &policyset) {
                // policy successfully validated, let's make sure we don't get any
                // dynamic type errors
                let authorizer = Authorizer::new();
                debug!("Policies: {policyset}");
                debug!("Entities: {entities}");
                for r in input.requests.into_iter() {
                    let q = ast::Request::from(r);
                    debug!("Request: {q}");
                    let ans = authorizer.is_authorized(q.clone(), &policyset, &entities);

                    let unexpected_errs = ans
                        .diagnostics
                        .errors
                        .iter()
                        .filter_map(|error| match error {
                            AuthorizationError::PolicyEvaluationError { error, .. } => {
                                match error.error_kind() {
                                    // Evaluation errors the validator should prevent.
                                    EvaluationErrorKind::UnspecifiedEntityAccess(_)
                                    | EvaluationErrorKind::RecordAttrDoesNotExist(_, _)
                                    | EvaluationErrorKind::EntityAttrDoesNotExist { .. }
                                    | EvaluationErrorKind::FailedExtensionFunctionLookup(_)
                                    | EvaluationErrorKind::TypeError { .. }
                                    | EvaluationErrorKind::WrongNumArguments { .. } => {
                                        Some(error.to_string())
                                    }
                                    // Evaluation errors it shouldn't prevent. Not
                                    // written with a catch all so that we must
                                    // consider if a new error type should cause
                                    // this target to fail.
                                    EvaluationErrorKind::EntityDoesNotExist(_)
                                    | EvaluationErrorKind::IntegerOverflow(_)
                                    | EvaluationErrorKind::InvalidRestrictedExpression(_)
                                    | EvaluationErrorKind::UnlinkedSlot(_)
                                    | EvaluationErrorKind::FailedExtensionFunctionApplication {
                                        ..
                                    }
                                    | EvaluationErrorKind::NonValue(_)
                                    | EvaluationErrorKind::RecursionLimit => None,
                                }
                            }
                        })
                        .collect::<Vec<_>>();

                    assert_eq!(
                        unexpected_errs,
                        Vec::<String>::new(),
                        "validated policy produced unexpected errors {unexpected_errs:?}!\npolicies:\n{policyset}\nentities:\n{entities}\nschema:\n{schemafile_string}\nrequest:\n{q}\n",
                    )
                }
            }
        }
    }
});
