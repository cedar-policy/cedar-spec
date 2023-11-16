/*
 * Copyright 2022-2023 Amazon.com, Inc. or its affiliates. All Rights Reserved.
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
use cedar_policy_core::authorizer::Authorizer;
use cedar_policy_core::entities::Entities;
use cedar_policy_generators::{
    abac::{ABACPolicy, ABACRequest},
    err::{Error, Result},
    hierarchy::{Hierarchy, HierarchyGenerator},
    schema::Schema,
    settings::ABACSettings,
};
use cedar_policy_validator::{
    ApplySpec, NamespaceDefinition, ValidationMode, Validator, ValidatorSchema,
};
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
    enable_unspecified_apply_spec: true,
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
const LOG_FILENAME_ERR_INCORRECT_FORMAT: &str = "./logs/err_incorrect_format.txt";
const LOG_FILENAME_ERR_OTHER: &str = "./logs/err_other.txt";
const LOG_FILENAME_ENTITIES_ERROR: &str = "./logs/err_entities.txt";

// In the below, "vyes" means the schema passed validation, while "vno" means we
// got to the point of running the validator but validation failed
const LOG_FILENAME_TOTAL_ENTITY_TYPES: &str = "./logs/schemastats/total_entity_types";
const LOG_FILENAME_TOTAL_ACTIONS: &str = "./logs/schemastats/total_actions";
const LOG_FILENAME_APPLIES_TO_NONE: &str = "./logs/schemastats/applies_to_none";
const LOG_FILENAME_APPLIES_TO_PRINCIPAL_NONE: &str = "./logs/schemastats/applies_to_principal_none";
const LOG_FILENAME_APPLIES_TO_RESOURCE_NONE: &str = "./logs/schemastats/applies_to_resource_none";
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
            Ok(_) => (),
        }
    }
    res
}

fn maybe_log_schemastats(schema: Option<&NamespaceDefinition>, suffix: &str) {
    if std::env::var("FUZZ_LOG_STATS").is_ok() {
        let schema = schema.expect("should be SOME if FUZZ_LOG_STATS is ok");
        checkpoint(
            LOG_FILENAME_TOTAL_ENTITY_TYPES.to_string()
                + "_"
                + suffix
                + "_"
                + &format!("{:03}", schema.entity_types.len()),
        );
        checkpoint(
            LOG_FILENAME_TOTAL_ACTIONS.to_string()
                + "_"
                + suffix
                + "_"
                + &format!("{:03}", schema.actions.len()),
        );
        for action in schema.actions.values() {
            match action.applies_to.as_ref() {
                None => checkpoint(LOG_FILENAME_APPLIES_TO_NONE.to_string() + "_" + suffix),
                Some(ApplySpec {
                    principal_types,
                    resource_types,
                    ..
                }) => {
                    match principal_types.as_ref() {
                        None => checkpoint(
                            LOG_FILENAME_APPLIES_TO_PRINCIPAL_NONE.to_string() + "_" + suffix,
                        ),
                        Some(tys) => checkpoint(
                            LOG_FILENAME_APPLIES_TO_PRINCIPAL_LEN.to_string()
                                + "_"
                                + suffix
                                + "_"
                                + &format!("{:03}", tys.len()),
                        ),
                    }
                    match resource_types.as_ref() {
                        None => checkpoint(
                            LOG_FILENAME_APPLIES_TO_RESOURCE_NONE.to_string() + "_" + suffix,
                        ),
                        Some(tys) => checkpoint(
                            LOG_FILENAME_APPLIES_TO_RESOURCE_LEN.to_string()
                                + "_"
                                + suffix
                                + "_"
                                + &format!("{:03}", tys.len()),
                        ),
                    }
                }
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

fn maybe_log_policystats(policy: &ast::StaticPolicy, suffix: &str) {
    if std::env::var("FUZZ_LOG_STATS").is_ok() {
        let total_subexpressions = policy.condition().subexpressions().count();
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
        let schema: Schema = log_err(Schema::arbitrary(SETTINGS.clone(), u), "generating_schema")?;
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
    // preserve the schemafile for later logging, if we'll need it
    let schemafile = if std::env::var("FUZZ_LOG_STATS").is_ok() {
        Some(input.schema.schemafile().clone())
    } else {
        None
    };
    // preserve the schema in string format, which may be needed for error messages later
    let schemafile_string = input.schema.schemafile_string();
    if let Ok(schema) = ValidatorSchema::try_from(input.schema) {
        debug!("Schema: {:?}", schema);
        checkpoint(LOG_FILENAME_SCHEMA_VALID);
        if let Ok(entities) = Entities::try_from(input.hierarchy.clone()) {
            checkpoint(LOG_FILENAME_HIERARCHY_VALID);
            let validator = Validator::new(schema);
            let mut policyset = ast::PolicySet::new();
            let policy: ast::StaticPolicy = input.policy.into();
            policyset.add_static(policy.clone()).unwrap();
            if passes_validation(&validator, &policyset) {
                checkpoint(LOG_FILENAME_VALIDATION_PASS);
                maybe_log_schemastats(schemafile.as_ref(), "vyes");
                maybe_log_hierarchystats(&input.hierarchy, "vyes");
                maybe_log_policystats(&policy, "vyes");
                // policy successfully validated, let's make sure we don't get any
                // dynamic type errors
                let authorizer = Authorizer::new();
                debug!("Policies: {policyset}");
                debug!("Entities: {entities}");
                for r in input.requests.into_iter() {
                    let q = ast::Request::from(r);
                    debug!("Request: {q}");
                    let ans = authorizer.is_authorized(q.clone(), &policyset, &entities);

                    let unexpected_errs = ans.diagnostics.errors.iter().filter_map(|error|
                        match error {
                            cedar_policy::AuthorizationError::PolicyEvaluationError { error, .. } => match error.error_kind() {
                                // Evaluation errors the validator should prevent.
                                cedar_policy::EvaluationErrorKind::UnspecifiedEntityAccess(_) |
                                cedar_policy::EvaluationErrorKind::RecordAttrDoesNotExist(_, _) |
                                cedar_policy::EvaluationErrorKind::EntityAttrDoesNotExist { .. } |
                                cedar_policy::EvaluationErrorKind::FailedExtensionFunctionLookup(_) |
                                cedar_policy::EvaluationErrorKind::TypeError { .. } |
                                cedar_policy::EvaluationErrorKind::WrongNumArguments { .. } => Some(error.to_string()),
                                // Evaluation errors it shouldn't prevent. Not
                                // written with a catch all so that we must
                                // consider if a new error type should cause
                                // this target to fail.
                                cedar_policy::EvaluationErrorKind::EntityDoesNotExist(_) |
                                cedar_policy::EvaluationErrorKind::IntegerOverflow(_) |
                                cedar_policy::EvaluationErrorKind::InvalidRestrictedExpression(_) |
                                cedar_policy::EvaluationErrorKind::UnlinkedSlot(_) |
                                cedar_policy::EvaluationErrorKind::FailedExtensionFunctionApplication { .. } |
                                cedar_policy::EvaluationErrorKind::NonValue(_) |
                                cedar_policy::EvaluationErrorKind::RecursionLimit => None,
                            }
                        }
                    ).collect::<Vec<_>>();

                    assert_eq!(
                        unexpected_errs,
                        Vec::<String>::new(),
                        "validated policy produced unexpected errors {unexpected_errs:?}!\npolicies:\n{policyset}\nentities:\n{entities}\nschema:\n{schemafile_string}\nrequest:\n{q}\n",
                    )
                }
            } else {
                maybe_log_schemastats(schemafile.as_ref(), "vno");
                maybe_log_hierarchystats(&input.hierarchy, "vno");
                maybe_log_policystats(&policy, "vno");
            }
        }
    }
});
