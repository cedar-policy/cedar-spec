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

use cedar_policy::integration_testing::{JsonRequest, JsonTest};
use cedar_policy::{AuthorizationError, Policy};
use cedar_policy_core::ast::{
    Context, EntityType, EntityUID, EntityUIDEntry, PolicySet, Request, RestrictedExpr,
};
use cedar_policy_core::authorizer::Response;
use cedar_policy_core::entities::{Entities, TypeAndId};
use cedar_policy_core::jsonvalue::JsonValueWithNoDuplicateKeys;
use cedar_policy_generators::collections::HashMap;
use cedar_policy_validator::{SchemaFragment, ValidationMode, Validator, ValidatorSchema};
use std::io::Write;
use std::path::Path;
use std::str::FromStr;

/// Dump testcase to a directory.
///
/// `dirname`: directory in which to dump the data for the testcase. Will be
/// created if it doesn't exist.
///
/// `testcasename`: a name to use for the testcase. Will be used in various
/// filenames etc.
pub fn dump(
    dirname: impl AsRef<Path>,
    testcasename: &str,
    schema: &SchemaFragment,
    policies: &PolicySet,
    entities: &Entities,
    requests: impl IntoIterator<Item = (Request, Response)>,
) -> std::io::Result<()> {
    // If the policy set cannot be re-parsed (which is possible with our current
    // generators), then ignore it. The corpus test format currently has no way
    // to convey that the input should fail to parse.
    if !well_formed(policies) {
        return Ok(());
    }

    let dirname = dirname.as_ref();
    std::fs::create_dir_all(dirname)?;

    let schema_filename = dirname.join(format!("{testcasename}.cedarschema.json"));
    let policies_filename = dirname.join(format!("{testcasename}.cedar"));
    let entities_filename = dirname.join(format!("{testcasename}.entities.json"));
    let testcase_filename = dirname.join(format!("{testcasename}.json"));

    let schema_file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .truncate(true)
        .open(&schema_filename)?;
    serde_json::to_writer_pretty(schema_file, &schema)?;

    let mut policies_file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .truncate(true)
        .open(&policies_filename)?;
    let static_policies: Vec<_> = policies
        .static_policies()
        .map(ToString::to_string)
        .collect();
    writeln!(policies_file, "{}", static_policies.join("\n"))?;

    let entities_file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .truncate(true)
        .open(&entities_filename)?;
    entities.write_to_json(entities_file).unwrap();

    let testcase_file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .truncate(true)
        .open(testcase_filename)?;
    serde_json::to_writer_pretty(
        testcase_file,
        &JsonTest {
            schema: schema_filename.display().to_string(),
            policies: policies_filename.display().to_string(),
            entities: entities_filename.display().to_string(),
            should_validate: passes_validation(schema.clone(), policies),
            requests: requests
                .into_iter()
                .enumerate()
                .map(|(i, (q, a))| JsonRequest {
                    desc: format!("Request {i}"),
                    principal: dump_request_var(q.principal()),
                    action: dump_request_var(q.action()),
                    resource: dump_request_var(q.resource()),
                    context: dump_context(
                        q.context()
                            .expect("`dump` does not support requests missing context"),
                    ),
                    enable_request_validation: true,
                    decision: a.decision,
                    reason: cedar_policy::Response::from(a.clone())
                        .diagnostics()
                        .reason()
                        .cloned()
                        .collect(),
                    errors: cedar_policy::Response::from(a)
                        .diagnostics()
                        .errors()
                        .map(AuthorizationError::id)
                        .cloned()
                        .collect(),
                })
                .collect(),
        },
    )?;

    Ok(())
}

/// Check whether a policy set can be successfully parsed
fn well_formed(policies: &PolicySet) -> bool {
    policies
        .static_policies()
        .map(ToString::to_string)
        .all(|p| Policy::from_str(&p).is_ok())
}

/// Check whether a policy set passes validation
fn passes_validation(schema: SchemaFragment, policies: &PolicySet) -> bool {
    if let Ok(schema) = ValidatorSchema::try_from(schema) {
        let validator = Validator::new(schema);
        validator
            .validate(policies, ValidationMode::default())
            .validation_passed()
    } else {
        false
    }
}

/// Dump the entity uid to a json value if it is specified, otherwise return `None`
fn dump_request_var(var: &EntityUIDEntry) -> Option<JsonValueWithNoDuplicateKeys> {
    match var {
        EntityUIDEntry::Unknown { .. } => {
            panic!("`dump` does not support requests with unknown fields")
        }
        EntityUIDEntry::Known { euid, .. } => match euid.entity_type() {
            EntityType::Unspecified => None,
            EntityType::Specified(_) => {
                let json = serde_json::to_value(TypeAndId::from(euid as &EntityUID))
                    .expect("failed to serialize euid")
                    .into();
                Some(json)
            }
        },
    }
}

/// Dump the context to a "natural" json value
fn dump_context(context: &Context) -> JsonValueWithNoDuplicateKeys {
    let context = context
        .iter()
        .map(|it| {
            it.map(|(k, pval)| {
                (
                    k.clone(),
                    RestrictedExpr::try_from(pval)
                        .unwrap()
                        .to_natural_json()
                        .unwrap(),
                )
            })
            .collect::<HashMap<_, _>>()
        })
        .unwrap_or_default();
    serde_json::to_value(context)
        .expect("failed to serialize context")
        .into()
}
