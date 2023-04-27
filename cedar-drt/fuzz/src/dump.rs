use crate::collections::HashMap;
use cedar_policy_core::ast::{EntityUIDEntry, PolicyID, PolicySet, Request};
use cedar_policy_core::authorizer::{Answer, Decision};
use cedar_policy_core::entities::Entities;
use cedar_policy_validator::SchemaFragment;
use serde::Serialize;
use std::io::Write;
use std::path::Path;

/// Dump testcase to a directory.
///
/// `dirname`: directory in which to dump the data for the testcase. Will be
/// created if it doesn't exist.
///
/// `testcasename`: a name to use for the testcase. Will be used in various
/// filenames etc.
///
/// `passes_validation`: whether the given policy passes validation with the
/// given schema
pub fn dump<'a>(
    dirname: impl AsRef<Path>,
    testcasename: &str,
    schema: &SchemaFragment,
    passes_validation: bool,
    policies: &PolicySet,
    entities: &Entities,
    requests: impl IntoIterator<Item = (&'a Request, &'a Answer)>,
) -> std::io::Result<()> {
    let dirname = dirname.as_ref();
    std::fs::create_dir_all(dirname)?;

    let schema_filename = dirname.join(format!("schema_{testcasename}.json"));
    let policies_filename = dirname.join(format!("policies_{testcasename}.txt"));
    let entities_filename = dirname.join(format!("entities_{testcasename}.txt"));
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
        &IntegrationTestCase {
            schema: &schema_filename,
            policies: &policies_filename,
            entities: &entities_filename,
            should_validate: passes_validation,
            queries: requests
                .into_iter()
                .enumerate()
                .map(|(i, (q, a))| IntegrationRequest {
                    desc: format!("Request {i}"),
                    principal: dump_request_var(q.principal()),
                    action: dump_request_var(q.action()),
                    resource: dump_request_var(q.resource()),
                    context: q
                        .context()
                        .map(|ctxt| {
                            ctxt.iter()
                                .map(|(k, expr)| (k.to_string(), expr.to_natural_json().unwrap()))
                                .collect::<HashMap<_, _>>()
                        })
                        .unwrap_or_default(),
                    decision: a.decision,
                    reasons: &a.diagnostics.reason,
                    errors: &a.diagnostics.errors,
                })
                .collect(),
        },
    )?;

    Ok(())
}

/// Dump the entity uid to a string if it is specified, otherwise return `None`,
/// which will appear as `null` in the JSON dump.
fn dump_request_var(var: &EntityUIDEntry) -> Option<String> {
    match var {
        EntityUIDEntry::Unknown => None,
        EntityUIDEntry::Concrete(euid) => match euid.entity_type() {
            cedar_policy_core::ast::EntityType::Unspecified => None,
            cedar_policy_core::ast::EntityType::Concrete(_) => Some(euid.to_string()),
        },
    }
}

/// Serde format for an integration test case
#[derive(Debug, Clone, Serialize)]
struct IntegrationTestCase<'a> {
    /// Schema filename
    schema: &'a Path,
    /// Policies filename
    policies: &'a Path,
    /// Whether the policies in the policies file should pass validation with
    /// the schema in the schema file
    should_validate: bool,
    /// Entities filename
    entities: &'a Path,
    /// One or more queries
    queries: Vec<IntegrationRequest<'a>>,
}

/// Serde format for an integration request
#[derive(Debug, Clone, Serialize)]
struct IntegrationRequest<'a> {
    /// Description of the behavior that we're testing/expecting.
    /// For the automated testcases we're dumping here, we don't use this for
    /// anything useful.
    desc: String,
    /// Principal
    principal: Option<String>,
    /// Action
    action: Option<String>,
    /// Resource
    resource: Option<String>,
    /// Context
    context: HashMap<String, serde_json::Value>,
    /// Decision
    decision: Decision,
    /// Reasons
    reasons: &'a std::collections::HashSet<PolicyID>,
    /// Errors
    errors: &'a [String],
}
