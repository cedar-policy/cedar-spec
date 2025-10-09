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
use cedar_drt_inner::{abac::FuzzTargetInput, fuzz_target};

use cedar_policy::{
    AuthorizationError, Authorizer, EvaluationError, Policy, PolicySet, Request, Schema,
    ValidationMode, Validator,
};

use libfuzzer_sys::arbitrary::{Arbitrary, Unstructured};
use log::debug;
use std::convert::TryFrom;

/// helper function that just tells us whether a policyset passes validation
fn passes_validation(validator: &Validator, policyset: &PolicySet, mode: ValidationMode) -> bool {
    validator.validate(policyset, mode).validation_passed()
}

// The main fuzz target. This is for PBT on the validator
fuzz_target!(|input: FuzzTargetInput<true>| {
    initialize_log();
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.schema.schemafile_string();
    if let Ok(schema) = Schema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
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
            debug!("Entities: {}", input.entities.as_ref());
            for r in input.requests.into_iter() {
                let q = Request::from(r);
                debug!("Request: {q}");
                let ans = authorizer.is_authorized(&q, &policyset, &input.entities);

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
                                | EvaluationError::WrongNumArguments(_) => Some(error.to_string()),
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
                    input.entities.as_ref()
                )
            }
        } else {
            assert!(
                !passes_strict,
                "policy fails permissive validation but passes strict validation!\npolicies:\n{policyset}\nentities:\n{}\nschema:\n{schemafile_string}\n",
                input.entities.as_ref()
            );
        }
    }
});
