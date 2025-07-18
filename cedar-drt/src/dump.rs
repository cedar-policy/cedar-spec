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

use cedar_policy::{AuthorizationError, Policy};
use cedar_policy_core::entities::TypeAndId;

use cedar_policy_generators::collections::HashMap;
use cedar_testing::cedar_test_impl::RustEngine;
use cedar_testing::integration_testing::{perform_integration_test, JsonRequest, JsonTest};
use std::{io::Write, path::Path, str::FromStr};

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
    schema: &cedar_policy::SchemaFragment,
    policies: &cedar_policy::PolicySet,
    entities: &cedar_policy::Entities,
    requests: impl IntoIterator<Item = (cedar_policy::Request, cedar_policy::Response)>,
) -> std::io::Result<()> {
    // If the policy set cannot be re-parsed (which is possible with our current
    // generators), then ignore it. The corpus test format currently has no way
    // to convey that the input should fail to parse.
    if !well_formed(policies) {
        return Ok(());
    }

    let dirname = dirname.as_ref();
    std::fs::create_dir_all(dirname)?;

    let schema_filename = dirname.join(format!("{testcasename}.cedarschema"));
    let policies_filename = dirname.join(format!("{testcasename}.cedar"));
    let entities_filename = dirname.join(format!("{testcasename}.entities.json"));
    let testcase_filename = dirname.join(format!("{testcasename}.json"));

    let mut schema_file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .truncate(true)
        .open(&schema_filename)?;
    let schema_text = schema.to_cedarschema().unwrap();
    writeln!(schema_file, "{schema_text}")?;

    let mut policies_file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .truncate(true)
        .open(&policies_filename)?;
    let static_policies: Vec<_> = policies
        .as_ref()
        .static_policies()
        .map(ToString::to_string)
        .collect();
    let policy_text = static_policies.join("\n");
    writeln!(policies_file, "{policy_text}")?;

    let entities_file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .truncate(true)
        .open(&entities_filename)?;
    entities.write_to_json(entities_file).unwrap();

    let requests: Vec<JsonRequest> = requests
        .into_iter()
        .enumerate()
        .map(|(i, (q, a))| JsonRequest {
            description: format!("Request {i}"),
            principal: dump_request_var(q.principal().unwrap()),
            action: dump_request_var(q.action().unwrap()),
            resource: dump_request_var(q.resource().unwrap()),
            context: dump_context(
                q.context()
                    .expect("`dump` does not support requests missing context")
                    .clone(),
            ),
            validate_request: true,
            decision: a.decision(),
            reason: cedar_policy::Response::from(a.clone())
                .diagnostics()
                .reason()
                .cloned()
                .collect(),
            errors: cedar_policy::Response::from(a)
                .diagnostics()
                .errors()
                .map(|e| match e {
                    AuthorizationError::PolicyEvaluationError(e) => e.policy_id(),
                })
                .cloned()
                .collect(),
        })
        .collect();

    let should_validate = passes_validation(schema.clone(), policies);

    let testcase = JsonTest {
        schema: schema_filename.display().to_string(),
        policies: policies_filename.display().to_string(),
        entities: entities_filename.display().to_string(),
        should_validate,
        requests: requests.clone(),
    };

    let testcase_file = std::fs::OpenOptions::new()
        .create(true)
        .write(true)
        .append(false)
        .truncate(true)
        .open(testcase_filename)?;
    serde_json::to_writer_pretty(testcase_file, &testcase)?;

    // The generated test case should successfully run
    check_test(
        policy_text,
        schema_text,
        entities,
        should_validate,
        requests,
        testcasename,
    );

    Ok(())
}

// Check that the generated test passes the `perform_integration_test` function
fn check_test(
    formatted_policies: String,
    formatted_schema: String,
    entities: &cedar_policy::Entities,
    should_validate: bool,
    requests: Vec<JsonRequest>,
    test_name: &str,
) {
    let parsed_policies = cedar_policy::PolicySet::from_str(&formatted_policies)
        .unwrap_or_else(|e| panic!("error re-parsing policy file: {e}"));

    let parsed_schema = cedar_policy::Schema::from_cedarschema_str(&formatted_schema)
        .unwrap_or_else(|e| panic!("error re-parsing schema: {e}"))
        .0;

    let parsed_entities = cedar_policy::Entities::from_json_value(
        entities.as_ref().to_json_value().unwrap(),
        Some(&parsed_schema),
    )
    .unwrap_or_else(|e| panic!("error re-parsing entities: {e}"));

    let rust_impl = RustEngine::new();

    perform_integration_test(
        &parsed_policies,
        &parsed_entities,
        &parsed_schema,
        should_validate,
        requests,
        test_name,
        &rust_impl,
    );
}

/// Check whether a policy set can be successfully parsed
fn well_formed(policies: &cedar_policy::PolicySet) -> bool {
    policies
        .as_ref()
        .static_policies()
        .map(ToString::to_string)
        .all(|p| Policy::from_str(&p).is_ok())
}

/// Check whether a policy set passes validation
fn passes_validation(
    schema: cedar_policy::SchemaFragment,
    policies: &cedar_policy::PolicySet,
) -> bool {
    if let Ok(schema) = schema.try_into() {
        let validator = cedar_policy::Validator::new(schema);
        validator
            .validate(policies, cedar_policy::ValidationMode::default())
            .validation_passed()
    } else {
        false
    }
}

/// Dump the entity uid to a json value
fn dump_request_var(var: &cedar_policy::EntityUid) -> serde_json::Value {
    let tyid = TypeAndId::from(var.as_ref());
    serde_json::to_value(tyid).expect("failed to serialize euid")
}

/// Dump the context to a "natural" json value
fn dump_context(context: cedar_policy::Context) -> serde_json::Value {
    let context = context
        .into_iter()
        .map(|(k, pval)| (k, pval.as_ref().to_natural_json().unwrap()))
        .collect::<HashMap<_, _>>();
    serde_json::to_value(context).expect("failed to serialize context")
}
