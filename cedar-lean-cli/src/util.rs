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
use crate::analysis::{AnalyzePolicyFindings, PerSigFindings, VacuityResult};
use crate::cli_enums::{ContextArg, RequestArgsEnum, ValidationMode};
use crate::err::{ContentType, EntityType, ExecError, RequestElement};
use cedar_policy::{
    Context, Entities, EntityId, EntityTypeName, EntityUid, Expression, Policy, PolicyId,
    PolicySet, Request, RequestEnv, Schema,
};
use itertools::Itertools;
use miette::WrapErr;
use serde::Serialize;
use serde_json::{from_str, Value};
use std::collections::HashSet;
use std::{fs::read_to_string, path::PathBuf, str::FromStr};

/// A struct reprensting which request environments to restrict the analysis to
/// we will check against all (well-formed) request environments restricted to
/// the `OpenRequestEnv`
pub struct OpenRequestEnv {
    principal_type: Option<EntityTypeName>,
    action_id: Option<EntityUid>,
    resource_type: Option<EntityTypeName>,
}

impl OpenRequestEnv {
    pub fn any() -> Self {
        Self {
            principal_type: None,
            action_id: None,
            resource_type: None,
        }
    }

    pub fn is_any(&self) -> bool {
        matches!(
            (&self.principal_type, &self.action_id, &self.resource_type),
            (None, None, None)
        )
    }

    fn principal_type_fmt(
        ptype: &EntityTypeName,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "principal ∈ {}", ptype)
    }

    fn action_id_fmt(aid: &EntityUid, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "action == {}", aid)
    }

    fn resource_type_fmt(
        rtype: &EntityTypeName,
        f: &mut std::fmt::Formatter<'_>,
    ) -> std::fmt::Result {
        write!(f, "resource ∈ {}", rtype)
    }
}

/// Add a pretty-print for OpenRequestEnv, if an element is not provided then it may be `any` such EntityType
impl std::fmt::Display for OpenRequestEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match (&self.principal_type, &self.action_id, &self.resource_type) {
            (None, None, None) => Ok(()),
            (Some(ptype), None, None) => Self::principal_type_fmt(ptype, f),
            (None, Some(aid), None) => Self::action_id_fmt(aid, f),
            (None, None, Some(rtype)) => Self::resource_type_fmt(rtype, f),
            (Some(ptype), Some(aid), None) => {
                Self::principal_type_fmt(ptype, f)?;
                write!(f, " and ")?;
                Self::action_id_fmt(aid, f)
            }
            (Some(ptype), None, Some(rtype)) => {
                Self::principal_type_fmt(ptype, f)?;
                write!(f, " and ")?;
                Self::resource_type_fmt(rtype, f)
            }
            (None, Some(aid), Some(rtype)) => {
                Self::action_id_fmt(aid, f)?;
                write!(f, " and ")?;
                Self::resource_type_fmt(rtype, f)
            }
            (Some(ptype), Some(aid), Some(rtype)) => {
                Self::principal_type_fmt(ptype, f)?;
                write!(f, ", ")?;
                Self::action_id_fmt(aid, f)?;
                write!(f, ", and ")?;
                Self::resource_type_fmt(rtype, f)
            }
        }
    }
}

/// A simple wrapper around Cedar's RequestEnv type to allow for pretty-printing
#[derive(Debug)]
pub enum ReqEnv {
    Env(RequestEnv),
}

impl std::fmt::Display for ReqEnv {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let req_env = match self {
            ReqEnv::Env(req_env) => req_env.clone(),
        };
        write!(
            f,
            "(PrincipalType: {0}, ActionName: {1}, ResourceType: {2})",
            req_env.principal().basename(),
            req_env.action().id().escaped(),
            req_env.resource().basename()
        )
    }
}

/// Convert from strings to Cedar Types.
impl OpenRequestEnv {
    fn entity_type_from_str(
        type_str: Option<String>,
        err_type: EntityType,
    ) -> Result<Option<EntityTypeName>, ExecError> {
        let type_str = match type_str {
            Option::None => return Ok(None),
            Some(type_str) => type_str,
        };
        match EntityTypeName::from_str(&type_str) {
            Ok(type_name) => Ok(Some(type_name)),
            Err(parse_err) => Err(ExecError::EntityTypeError {
                entity_type: err_type,
                input_str: type_str,
                error: Box::new(parse_err),
            }),
        }
    }

    fn action_id_from_str(action_name: Option<String>) -> Option<EntityUid> {
        let action_name = action_name?;
        let action_type = EntityTypeName::from_str("Action").unwrap();
        let action_id = EntityId::from_str(&action_name).unwrap();
        Some(EntityUid::from_type_name_and_id(action_type, action_id))
    }

    pub fn new(
        principal_type: Option<String>,
        action_name: Option<String>,
        resource_type: Option<String>,
    ) -> Result<OpenRequestEnv, ExecError> {
        let principal_type =
            Self::entity_type_from_str(principal_type, EntityType::PrincipalTypeName)?;
        let action_id = Self::action_id_from_str(action_name);
        let resource_type =
            Self::entity_type_from_str(resource_type, EntityType::ResourceTypeName)?;

        Ok(OpenRequestEnv {
            principal_type,
            action_id,
            resource_type,
        })
    }

    /// Convert a OpenRequestEnv to a vector of RequestEnv that are
    /// 1) consistent with OpenRequestEnv, and
    /// 2) consistent with the provided `schema`
    ///
    /// if `self` specifies any component and there are no (principal, action, resource)
    /// consistent with both `self` and `schema`, then an error will be thrown. Otherwise,
    /// if the schema has no such request environments, then an empty vector is returned.
    pub fn to_request_envs(&self, schema: &Schema) -> Result<Vec<RequestEnv>, ExecError> {
        let action_ids = schema
            .action_entities()?
            .into_iter()
            .map(|action| action.uid());
        let mut req_envs: Vec<RequestEnv> = Vec::new();
        for action_id in action_ids {
            match &self.action_id {
                // only compare ids rather than full uids because JSON schemas append additional
                // namespaces before action.
                Some(req_act_id) if (*req_act_id).id() != action_id.id() => continue,
                _ => (),
            };
            if let Some(principal_types) = schema.principals_for_action(&action_id) {
                for principal_type in principal_types {
                    match &self.principal_type {
                        Some(req_principal_type) if req_principal_type != principal_type => {
                            continue
                        }
                        _ => (),
                    };
                    if let Some(resource_types) = schema.resources_for_action(&action_id) {
                        for resource_type in resource_types {
                            match &self.resource_type {
                                Some(req_resource_type) if req_resource_type != resource_type => {
                                    continue
                                }
                                _ => (),
                            };
                            let req_env = RequestEnv::new(
                                principal_type.clone(),
                                action_id.clone(),
                                resource_type.clone(),
                            );
                            req_envs.push(req_env)
                        }
                    }
                }
            }
        }
        if req_envs.is_empty()
            && (self.action_id.is_some()
                || self.principal_type.is_some()
                || self.resource_type.is_some())
        {
            return Err(ExecError::RequestEnvArgsIncompatible {
                principal_type: match &self.principal_type {
                    Some(principal_type) => principal_type.basename().into(),
                    _ => "Every principal".into(),
                },
                action_name: match &self.action_id {
                    Some(action_id) => action_id.id().escaped().into(),
                    _ => "perform any action".into(),
                },
                resource_type: match &self.resource_type {
                    Some(resource_type) => resource_type.basename().into(),
                    _ => "any resource".into(),
                },
            });
        }
        // Make determinstic order to make CLI more usable for error detection
        req_envs.sort();
        Ok(req_envs)
    }
}

/// Auxilary function that parses a Policy, simple wrapper around cedar::Policy::from_str
pub fn parse_policy(fname: &PathBuf) -> Result<Policy, ExecError> {
    match read_to_string(fname) {
        Ok(policy_text) => match Policy::from_str(policy_text.as_str()) {
            Ok(policy) => Ok(rename_from_id_annotation_policy(policy)),
            Err(parse_err) => Err(ExecError::ParseError {
                content_type: ContentType::Policy,
                file_name: fname.to_path_buf(),
                error: Box::new(parse_err),
            }),
        },
        Err(read_error) => Err(ExecError::FileReadError {
            content_type: ContentType::Policy,
            file_name: fname.to_path_buf(),
            error: Box::new(read_error),
        }),
    }
}

fn rename_from_id_annotation_policy(policy: Policy) -> Policy {
    match policy.annotation("id") {
        None => policy,
        Some(anno) => anno
            .parse()
            .map(|id| policy.new_id(id))
            .unwrap_or_else(|never| match never {}),
    }
}

/// Auxilary function that parses a PolicySet, simple wrapper around cedar::PolicySet::from_str
pub fn parse_policyset(fname: &PathBuf) -> Result<PolicySet, ExecError> {
    match read_to_string(fname) {
        Ok(policyset_text) => match PolicySet::from_str(policyset_text.as_str()) {
            Ok(policyset) => match rename_from_id_annotation_policyset(policyset) {
                Ok(pset) => Ok(pset),
                Err(err) => Err(ExecError::RenameIdError {
                    content_type: ContentType::PolicySet,
                    file_name: fname.to_path_buf(),
                    error: err,
                }),
            },
            Err(parse_err) => Err(ExecError::ParseError {
                content_type: ContentType::PolicySet,
                file_name: fname.to_path_buf(),
                error: Box::new(parse_err),
            }),
        },
        Err(read_error) => Err(ExecError::FileReadError {
            content_type: ContentType::PolicySet,
            file_name: fname.to_path_buf(),
            error: Box::new(read_error),
        }),
    }
}

fn rename_from_id_annotation_policyset(ps: PolicySet) -> miette::Result<PolicySet> {
    let mut new_ps = PolicySet::new();
    let t_iter = ps.templates().map(|t| match t.annotation("id") {
        None => Ok(t.clone()),
        Some(anno) => anno.parse().map(|a| t.new_id(a)),
    });
    for t in t_iter {
        let template = t.unwrap_or_else(|never| match never {});
        new_ps
            .add_template(template)
            .wrap_err("failed to add template to policy set")?;
    }
    let p_iter = ps.policies().map(|p| match p.annotation("id") {
        None => Ok(p.clone()),
        Some(anno) => anno.parse().map(|a| p.new_id(a)),
    });
    for p in p_iter {
        let policy = p.unwrap_or_else(|never| match never {});
        new_ps
            .add(policy)
            .wrap_err("failed to add template to policy set")?;
    }
    Ok(new_ps)
}

/// Auxilary function that parses a Schema
/// if the schema-file name ends in .json use JSON format, otherwise
/// use the cedar-schema format.
pub fn parse_schema(fname: &PathBuf) -> Result<Schema, ExecError> {
    match read_to_string(fname) {
        Ok(schema_text) => {
            let is_json_schema = fname.extension().is_some_and(|ext| ext == "json");
            if is_json_schema {
                match Schema::from_json_str(schema_text.as_str()) {
                    Ok(schema) => Ok(schema),
                    Err(schema_err) => Err(ExecError::ParseError {
                        content_type: ContentType::SchemaJSON,
                        file_name: fname.to_path_buf(),
                        error: Box::new(schema_err),
                    }),
                }
            } else {
                match Schema::from_str(schema_text.as_str()) {
                    Ok(schema) => Ok(schema),
                    Err(schema_err) => Err(ExecError::ParseError {
                        content_type: ContentType::Schema,
                        file_name: fname.to_path_buf(),
                        error: Box::new(schema_err),
                    }),
                }
            }
        }
        Err(read_error) => Err(ExecError::FileReadError {
            content_type: ContentType::Schema,
            file_name: fname.to_path_buf(),
            error: Box::new(read_error),
        }),
    }
}

/// Auxillary function used to parse a file containing Cedar Entities
pub fn parse_entities(fname: &PathBuf, schema: Option<&Schema>) -> Result<Entities, ExecError> {
    match read_to_string(fname) {
        Ok(entities_json_str) => match Entities::from_json_str(&entities_json_str, schema) {
            Ok(entities) => Ok(entities),
            Err(e) => Err(ExecError::ParseError {
                content_type: ContentType::Entities,
                file_name: fname.to_path_buf(),
                error: Box::new(e),
            }),
        },
        Err(read_error) => Err(ExecError::FileReadError {
            content_type: ContentType::Entities,
            file_name: fname.to_path_buf(),
            error: Box::new(read_error),
        }),
    }
}

/// Auxillary function used to parse a file containing a Cedar Expression
pub fn parse_expression(fname: &PathBuf) -> Result<Expression, ExecError> {
    match read_to_string(fname) {
        Ok(expr_str) => match Expression::from_str(&expr_str) {
            Ok(expr) => Ok(expr),
            Err(e) => Err(ExecError::ParseError {
                content_type: ContentType::Expression,
                file_name: fname.to_path_buf(),
                error: Box::new(e),
            }),
        },
        Err(read_error) => Err(ExecError::FileReadError {
            content_type: ContentType::Expression,
            file_name: fname.to_path_buf(),
            error: Box::new(read_error),
        }),
    }
}

impl ContextArg {
    /// Parses a ContextArg into a Cedar Context struct
    pub fn parse(self, schema: Option<(&Schema, &EntityUid)>) -> Result<Context, ExecError> {
        match self {
            Self::Default => Ok(Context::empty()),
            Self::FromString { json_str } => match Context::from_json_str(&json_str, schema) {
                Ok(c) => Ok(c),
                Err(e) => Err(ExecError::RequestError {
                    element: RequestElement::Context,
                    input_str: json_str,
                    error: Box::new(e),
                }),
            },
            Self::FromFile { file_name } => match read_to_string(&file_name) {
                Ok(json_str) => match Context::from_json_str(&json_str, schema) {
                    Ok(c) => Ok(c),
                    Err(e) => Err(ExecError::ParseError {
                        content_type: ContentType::Context,
                        file_name: file_name.to_path_buf(),
                        error: Box::new(e),
                    }),
                },
                Err(e) => Err(ExecError::FileReadError {
                    content_type: ContentType::Context,
                    file_name: file_name.to_path_buf(),
                    error: Box::new(e),
                }),
            },
        }
    }
}

/// Auxillary function that converts a string to an Cedar EntityUid
fn parse_entity_uid(input_str: String, element: RequestElement) -> Result<EntityUid, ExecError> {
    match EntityUid::from_str(&input_str) {
        Ok(euid) => Ok(euid),
        Err(e) => Err(ExecError::RequestError {
            element,
            input_str,
            error: Box::new(e),
        }),
    }
}

/// Auxillary function used to convert CLI arguments into a Cedar Request struct
fn request_from_args(
    principal: String,
    action: String,
    resource: String,
    context: ContextArg,
    schema: Option<&Schema>,
) -> Result<Request, ExecError> {
    let principal = parse_entity_uid(principal, RequestElement::Principal)?;
    let action = parse_entity_uid(action, RequestElement::Action)?;
    let resource = parse_entity_uid(resource, RequestElement::Resource)?;
    let schema = schema.map(|schema| (schema, &action));
    let context = context.parse(schema)?;
    match Request::new(principal, action, resource, context, None) {
        Ok(r) => Ok(r),
        Err(e) => Err(ExecError::RequestValidationError { error: Box::new(e) }),
    }
}

/// Auxillary function used to help parse JSON values
fn string_from_value(v: Option<&Value>) -> Option<String> {
    match v {
        Some(Value::String(s)) => Some(s.clone()),
        _ => None,
    }
}

/// Auxillary function used to convert a JSON representation of a request into a Cedar Request struct
fn request_from_json_value(
    v: Value,
    fname: PathBuf,
    schema: Option<&Schema>,
) -> Result<Request, ExecError> {
    let principal = string_from_value(v.get("principal"));
    let action = string_from_value(v.get("action"));
    let resource = string_from_value(v.get("resource"));
    let context = v.get("context");
    match (principal, action, resource, context) {
        (Some(p), Some(a), Some(r), Some(c)) => request_from_args(
            p,
            a,
            r,
            ContextArg::FromString {
                json_str: c.to_string(),
            },
            schema,
        ),
        _ => Err(ExecError::ParseJsonError {
            content_type: ContentType::Request,
            file_name: fname,
        }),
    }
}

impl RequestArgsEnum {
    /// A function that parses a RequestArgEnum into a Cedar Request struct
    pub fn parse(self, schema: Option<&Schema>) -> Result<Request, ExecError> {
        match self {
            Self::FromArgs {
                principal,
                action,
                resource,
                context,
            } => request_from_args(principal, action, resource, context, schema),
            Self::FromFile { file_name } => match read_to_string(&file_name) {
                Ok(json_str) => match from_str::<Value>(&json_str) {
                    Ok(v) => request_from_json_value(v, file_name, schema),
                    Err(e) => Err(ExecError::ParseError {
                        content_type: ContentType::Request,
                        file_name,
                        error: Box::new(e),
                    }),
                },
                Err(e) => Err(ExecError::FileReadError {
                    content_type: ContentType::Request,
                    file_name,
                    error: Box::new(e),
                }),
            },
        }
    }
}

/// Convert from our ValidationMode enum to Cedar ValidationMode enum
impl ValidationMode {
    pub fn to_cedar(self) -> cedar_policy::ValidationMode {
        match self {
            Self::Strict => cedar_policy::ValidationMode::Strict,
        }
    }
}

/// Helper classes for printing findings to json
#[derive(Serialize, Debug, Clone)]
pub struct RequestEnvSer {
    pub principal_type: String,
    pub action_uid: String,
    pub resource_type: String,
}

impl RequestEnvSer {
    pub fn new(req_env: &RequestEnv) -> Self {
        RequestEnvSer {
            principal_type: req_env.principal().basename().to_string(),
            action_uid: req_env.action().id().escaped().to_string(),
            resource_type: req_env.resource().basename().to_string(),
        }
    }
}

#[derive(Debug, Clone, Serialize)]
struct PolicySer {
    policy_id: PolicyId,
    policy_str: String,
}

impl PolicySer {
    fn new(policy_id: &PolicyId, policy_set: &PolicySet) -> Self {
        let policy_str = policy_set.policy(policy_id).unwrap().to_cedar().unwrap();
        PolicySer {
            policy_id: policy_id.clone(),
            policy_str,
        }
    }

    fn from_set(pid_set: &HashSet<PolicyId>, policy_set: &PolicySet) -> Vec<PolicySer> {
        pid_set
            .iter()
            .map(|pid| PolicySer::new(pid, policy_set))
            .collect_vec()
    }
}

#[derive(Debug, Clone, Serialize)]
struct PermitShadowedByPermit {
    permit: PolicySer,
    shadowing_permits: Vec<PolicySer>,
}

#[derive(Debug, Clone, Serialize)]
struct ForbidShadowedByForbids {
    forbid: PolicySer,
    shadowing_forbids: Vec<PolicySer>,
}

#[derive(Debug, Clone, Serialize)]
struct PermitOverridenByForbids {
    permit: PolicySer,
    overriding_forbids: Vec<PolicySer>,
}

#[derive(Debug, Clone, Serialize)]
struct EquivalentPolicies {
    equivalent_policies: Vec<PolicySer>,
}

#[derive(Debug, Clone, Serialize)]
struct VacuityFinding {
    policy: PolicySer,
    status: VacuityResult,
}

#[derive(Debug, Clone, Serialize)]
struct PerSigFindingsSer {
    req_env: RequestEnvSer,
    equiv_classes: Vec<EquivalentPolicies>,
    permit_shadowed_by_permits: Vec<PermitShadowedByPermit>,
    forbid_shadowed_by_forbids: Vec<ForbidShadowedByForbids>,
    permit_overriden_by_forbids: Vec<PermitOverridenByForbids>,
}

impl PerSigFindingsSer {
    fn new(per_sig_findings: &PerSigFindings, policy_set: &PolicySet) -> Self {
        let equiv_classes = per_sig_findings
            .equiv_classes
            .iter()
            .filter_map(|pid_set| {
                if pid_set.is_empty() {
                    None
                } else {
                    Some(EquivalentPolicies {
                        equivalent_policies: PolicySer::from_set(pid_set, policy_set),
                    })
                }
            })
            .collect_vec();

        let permit_shadowed_by_permits = per_sig_findings
            .permit_shadowed_by_permits
            .iter()
            .filter_map(|(pid, pid_set)| {
                if pid_set.is_empty() {
                    None
                } else {
                    Some(PermitShadowedByPermit {
                        permit: PolicySer::new(pid, policy_set),
                        shadowing_permits: PolicySer::from_set(pid_set, policy_set),
                    })
                }
            })
            .collect_vec();
        let forbid_shadowed_by_forbids = per_sig_findings
            .forbid_shadowed_by_forbids
            .iter()
            .filter_map(|(pid, pid_set)| {
                if pid_set.is_empty() {
                    None
                } else {
                    Some(ForbidShadowedByForbids {
                        forbid: PolicySer::new(pid, policy_set),
                        shadowing_forbids: PolicySer::from_set(pid_set, policy_set),
                    })
                }
            })
            .collect_vec();

        let permit_overriden_by_forbids = per_sig_findings
            .permit_overriden_by_forbids
            .iter()
            .filter_map(|(pid, pid_set)| {
                if pid_set.is_empty() {
                    None
                } else {
                    Some(PermitOverridenByForbids {
                        permit: PolicySer::new(pid, policy_set),
                        overriding_forbids: PolicySer::from_set(pid_set, policy_set),
                    })
                }
            })
            .collect_vec();
        PerSigFindingsSer {
            req_env: per_sig_findings.req_env.clone(),
            equiv_classes,
            permit_shadowed_by_permits,
            forbid_shadowed_by_forbids,
            permit_overriden_by_forbids,
        }
    }
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct AnalyzePolicyFindingsSer {
    vacuous_result: VacuityResult,
    vacuous_policies: Vec<VacuityFinding>,
    per_sig_findings: Vec<PerSigFindingsSer>,
}

impl AnalyzePolicyFindingsSer {
    pub(crate) fn new(analyze_findings: &AnalyzePolicyFindings, policy_set: &PolicySet) -> Self {
        let vacuous_policies = analyze_findings
            .vacuous_policies
            .iter()
            .map(|(pid, res)| VacuityFinding {
                policy: PolicySer::new(pid, policy_set),
                status: *res,
            })
            .collect_vec();
        let per_sig_findings = analyze_findings
            .per_sig_findings
            .iter()
            .map(|findings| PerSigFindingsSer::new(findings, policy_set))
            .collect_vec();
        AnalyzePolicyFindingsSer {
            vacuous_result: analyze_findings.vacuous_result,
            vacuous_policies,
            per_sig_findings,
        }
    }
}
