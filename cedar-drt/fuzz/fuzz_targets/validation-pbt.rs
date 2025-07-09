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
use cedar_drt::{fuzz_target, logger::initialize_log};

use cedar_policy::{
    AuthorizationError, Authorizer, Entities, EvaluationError, Policy, PolicySet, Request, Schema,
    ValidationMode, Validator,
};

use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    err::{Error, Result},
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema,
    settings::ABACSettings,
};
use itertools::Itertools;
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
    match_types: false,
    enable_extensions: true,
    max_depth: 7,
    max_width: 7,
    enable_additional_attributes: true,
    enable_like: true,
    enable_action_groups_and_attrs: true,
    enable_arbitrary_func_call: true,
    enable_unknowns: false,
    enable_action_in_constraints: true,
};

const LOG_FILENAME_GENERATION_START: &str = "./logs/01_generation_start.txt";
const LOG_FILENAME_GENERATED_SCHEMA: &str = "./logs/02_generated_schema.txt";
const LOG_FILENAME_GENERATED_HIERARCHY: &str = "./logs/03_generated_hierarchy.txt";
const LOG_FILENAME_GENERATED_POLICY: &str = "./logs/04_generated_policy.txt";
const LOG_FILENAME_GENERATED_REQUESTS: &str = "./logs/05_generated_requests.txt";
const LOG_FILENAME_SCHEMA_VALID: &str = "./logs/06_schema_valid.txt";
const LOG_FILENAME_HIERARCHY_VALID: &str = "./logs/07_hierarchy_valid.txt";
const LOG_FILENAME_VALIDATION_PASS: &str = "./logs/08_validation_pass.txt";

const LOG_FILENAME_ERR_NOT_ENOUGH_DATA: &str = "./logs/err_not_enough_data.txt";
const LOG_FILENAME_ERR_EMPTY_CHOOSE: &str = "./logs/err_empty_choose.txt";
const LOG_FILENAME_ERR_TOO_DEEP: &str = "./logs/err_too_deep.txt";
const LOG_FILENAME_ERR_NO_VALID_TYPES: &str = "./logs/err_no_valid_types.txt";
const LOG_FILENAME_ERR_EXTENSIONS_DISABLED: &str = "./logs/err_extensions_disabled.txt";
const LOG_FILENAME_ERR_LIKE_DISABLED: &str = "./logs/err_like_disabled.txt";
const LOG_FILENAME_ERR_CONTEXT: &str = "./logs/err_context.txt";
const LOG_FILENAME_ERR_INCORRECT_FORMAT: &str = "./logs/err_incorrect_format.txt";
const LOG_FILENAME_ERR_OTHER: &str = "./logs/err_other.txt";
const LOG_FILENAME_ENTITIES_ERROR: &str = "./logs/err_entities.txt";
const LOG_FILENAME_SCHEMA_ERROR: &str = "./logs/err_schema.txt";
const LOG_FILENAME_TOO_MANY_REQ_ENVS_ERROR: &str = "./logs/err_too_many_req_envs.txt";

// In the below, "vyes" means the schema passed validation, while "vno" means we
// got to the point of running the validator but validation failed
const LOG_FILENAME_TOTAL_ENTITY_TYPES: &str = "./logs/schemastats/total_entity_types";
const LOG_FILENAME_TOTAL_ACTIONS: &str = "./logs/schemastats/total_actions";
const LOG_FILENAME_APPLIES_TO_NONE: &str = "./logs/schemastats/applies_to_none";
const LOG_FILENAME_APPLIES_TO_PRINCIPAL_LEN: &str = "./logs/schemastats/applies_to_principal_len";
const LOG_FILENAME_APPLIES_TO_RESOURCE_LEN: &str = "./logs/schemastats/applies_to_resource_len";
const LOG_FILENAME_TOTAL_ENTITIES: &str = "./logs/hierarchystats/total_entities";
const LOG_FILENAME_TOTAL_SUBEXPRESSIONS: &str = "./logs/policystats/total_subexpressions";

/// Append to the given filename to indicate we've reached the corresponding
/// checkpoint, or the corresponding event has happened
fn checkpoint(filename: impl AsRef<std::path::Path>) {
    if std::env::var("FUZZ_LOG_STATS").is_ok() {
        use std::io::Write;
        let mut file = std::fs::OpenOptions::new()
            .create(true)
            .append(true)
            .open(filename.as_ref())
            .unwrap();
        writeln!(file, "y").unwrap();
    }
}

fn log_err<T>(res: Result<T>, doing_what: &str) -> Result<T> {
    if std::env::var("FUZZ_LOG_STATS").is_ok() {
        match &res {
            Err(Error::EntitiesError(_)) => {
                checkpoint(LOG_FILENAME_ENTITIES_ERROR.to_string() + "_" + doing_what)
            }
            Err(Error::SchemaError(_)) => {
                checkpoint(LOG_FILENAME_SCHEMA_ERROR.to_string() + "_" + doing_what)
            }
            Err(Error::NotEnoughData) => {
                checkpoint(LOG_FILENAME_ERR_NOT_ENOUGH_DATA.to_string() + "_" + doing_what)
            }
            Err(Error::EmptyChoose {
                doing_what: doing_2,
            }) => checkpoint(
                LOG_FILENAME_ERR_EMPTY_CHOOSE.to_string()
                    + "_"
                    + doing_what
                    + "_"
                    + &doing_2.replace(' ', "_"),
            ),
            Err(Error::TooDeep) => {
                checkpoint(LOG_FILENAME_ERR_TOO_DEEP.to_string() + "_" + doing_what)
            }
            Err(Error::NoValidPrincipalOrResourceTypes) => {
                checkpoint(LOG_FILENAME_ERR_NO_VALID_TYPES.to_string() + "_" + doing_what)
            }
            Err(Error::ExtensionsDisabled) => {
                checkpoint(LOG_FILENAME_ERR_EXTENSIONS_DISABLED.to_string() + "_" + doing_what)
            }
            Err(Error::LikeDisabled) => {
                checkpoint(LOG_FILENAME_ERR_LIKE_DISABLED.to_string() + "_" + doing_what)
            }
            Err(Error::ContextError(_)) => {
                checkpoint(LOG_FILENAME_ERR_CONTEXT.to_string() + "_" + doing_what)
            }
            Err(Error::IncorrectFormat {
                doing_what: doing_2,
            }) => checkpoint(
                LOG_FILENAME_ERR_INCORRECT_FORMAT.to_string()
                    + "_"
                    + doing_what
                    + "_"
                    + &doing_2.replace(' ', "_"),
            ),
            Err(Error::OtherArbitrary(_)) => {
                checkpoint(LOG_FILENAME_ERR_OTHER.to_string() + "_" + doing_what)
            }
            Err(Error::TooManyReqEnvs(_)) => {
                checkpoint(LOG_FILENAME_TOO_MANY_REQ_ENVS_ERROR.to_string() + "_" + doing_what)
            }
            Ok(_) => (),
        }
    }
    res
}

fn maybe_log_schemastats(schema: Option<&Schema>, suffix: &str) {
    if std::env::var("FUZZ_LOG_STATS").is_ok() {
        let schema = schema.expect("should be SOME if FUZZ_LOG_STATS is ok");
        checkpoint(
            LOG_FILENAME_TOTAL_ENTITY_TYPES.to_string()
                + "_"
                + suffix
                + "_"
                + &format!("{:03}", schema.entity_types().collect_vec().len()),
        );
        checkpoint(
            LOG_FILENAME_TOTAL_ACTIONS.to_string()
                + "_"
                + suffix
                + "_"
                + &format!("{:03}", schema.actions().collect_vec().len()),
        );
        for action in schema.actions() {
            let n_principals = schema
                .principals_for_action(action)
                .unwrap()
                .collect_vec()
                .len();
            let n_resources = schema
                .resources_for_action(action)
                .unwrap()
                .collect_vec()
                .len();
            // Cartesian product is empty. So action applies to None
            if n_principals == 0 || n_resources == 0 {
                checkpoint(LOG_FILENAME_APPLIES_TO_NONE.to_string() + "_" + suffix);
            } else {
                checkpoint(
                    LOG_FILENAME_APPLIES_TO_PRINCIPAL_LEN.to_string()
                        + "_"
                        + suffix
                        + "_"
                        + &format!("{:03}", n_principals),
                );
                checkpoint(
                    LOG_FILENAME_APPLIES_TO_RESOURCE_LEN.to_string()
                        + "_"
                        + suffix
                        + "_"
                        + &format!("{:03}", n_resources),
                );
            }
        }
    }
}

fn maybe_log_hierarchystats(hierarchy: &Hierarchy, suffix: &str) {
    if std::env::var("FUZZ_LOG_STATS").is_ok() {
        checkpoint(
            LOG_FILENAME_TOTAL_ENTITIES.to_string()
                + "_"
                + suffix
                + "_"
                + &format!("{:03}", hierarchy.num_entities()),
        );
    }
}

fn maybe_log_policystats(policy: &Policy, suffix: &str) {
    if std::env::var("FUZZ_LOG_STATS").is_ok() {
        let total_subexpressions = policy.as_ref().condition().subexpressions().count();
        checkpoint(
            LOG_FILENAME_TOTAL_SUBEXPRESSIONS.to_string()
                + "_"
                + suffix
                + "_"
                + &format!("{:03}", total_subexpressions),
        );
    }
}

impl<'a> Arbitrary<'a> for FuzzTargetInput {
    fn arbitrary(u: &mut Unstructured<'a>) -> arbitrary::Result<Self> {
        checkpoint(LOG_FILENAME_GENERATION_START);
        let schema: schema::Schema = log_err(
            schema::Schema::arbitrary(SETTINGS.clone(), u),
            "generating_schema",
        )?;
        checkpoint(LOG_FILENAME_GENERATED_SCHEMA);
        let hierarchy = log_err(schema.arbitrary_hierarchy(u), "generating_hierarchy")?;
        checkpoint(LOG_FILENAME_GENERATED_HIERARCHY);
        let policy = log_err(schema.arbitrary_policy(&hierarchy, u), "generating_policy")?;
        checkpoint(LOG_FILENAME_GENERATED_POLICY);
        let requests = [
            log_err(
                schema.arbitrary_request(&hierarchy, u),
                "generating_request",
            )?,
            log_err(
                schema.arbitrary_request(&hierarchy, u),
                "generating_request",
            )?,
            log_err(
                schema.arbitrary_request(&hierarchy, u),
                "generating_request",
            )?,
            log_err(
                schema.arbitrary_request(&hierarchy, u),
                "generating_request",
            )?,
            log_err(
                schema.arbitrary_request(&hierarchy, u),
                "generating_request",
            )?,
            log_err(
                schema.arbitrary_request(&hierarchy, u),
                "generating_request",
            )?,
            log_err(
                schema.arbitrary_request(&hierarchy, u),
                "generating_request",
            )?,
            log_err(
                schema.arbitrary_request(&hierarchy, u),
                "generating_request",
            )?,
        ];
        checkpoint(LOG_FILENAME_GENERATED_REQUESTS);
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
        checkpoint(LOG_FILENAME_SCHEMA_VALID);
        if let Ok(entities) = Entities::try_from(input.hierarchy.clone()) {
            checkpoint(LOG_FILENAME_HIERARCHY_VALID);
            let validator = Validator::new(schema.clone());
            let mut policyset = PolicySet::new();
            let policy: Policy = input.policy.into();
            policyset.add(policy.clone()).unwrap();
            let passes_strict = passes_validation(&validator, &policyset, ValidationMode::Strict);
            let passes_permissive =
                passes_validation(&validator, &policyset, ValidationMode::Permissive);
            if passes_permissive {
                checkpoint(LOG_FILENAME_VALIDATION_PASS);
                let suffix = if passes_strict { "vyes" } else { "vpermissive" };
                maybe_log_schemastats(Some(&schema), suffix);
                maybe_log_hierarchystats(&input.hierarchy, suffix);
                maybe_log_policystats(&policy, suffix);
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
                            AuthorizationError::PolicyEvaluationError(error) => {
                                match error.inner() {
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
                        .collect_vec();

                    assert_eq!(
                        unexpected_errs,
                        Vec::<String>::new(),
                        "validated policy produced unexpected errors {unexpected_errs:?}!\npolicies:\n{policyset}\nentities:\n{}\nschema:\n{schemafile_string}\nrequest:\n{q}\n",
                        entities.as_ref()
                    )
                }
            } else {
                maybe_log_schemastats(Some(&schema), "vno");
                maybe_log_hierarchystats(&input.hierarchy, "vno");
                maybe_log_policystats(&policy, "vno");
                assert!(
                    !passes_strict,
                    "policy fails permissive validation but passes strict validation!\npolicies:\n{policyset}\nentities:\n{}\nschema:\n{schemafile_string}\n",
                    entities.as_ref()
                );
            }
        }
    }
});
