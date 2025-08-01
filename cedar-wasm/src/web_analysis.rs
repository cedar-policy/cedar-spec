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
use crate::web_util::{AnalyzePolicyFindingsSer, OpenRequestEnv, RequestEnvSer};
use crate::web_err::ExecError;
use amzn_cedar_sym_eval::{wasm_solver::WasmCvc5Solver, SymCompiler, SymEnv};
use cedar_policy::{Effect, RequestEnv, Schema};
use cedar_policy_core::ast::{Policy, PolicySet, PolicyID};
use itertools::Itertools;
// use prettytable::{Attr, Cell, Row, Table};
use serde::Serialize;
use std::{
    collections::{HashMap, HashSet},
    iter::zip,
    sync::{Mutex, OnceLock},
};

// Global solver instance for web_analysis
static GLOBAL_ANALYSIS_SOLVER: OnceLock<Mutex<Option<SymCompiler<WasmCvc5Solver>>>> = OnceLock::new();

// Get or create the global analysis compiler
fn get_global_analysis_compiler() -> Result<&'static Mutex<Option<SymCompiler<WasmCvc5Solver>>>, ExecError> {
    Ok(GLOBAL_ANALYSIS_SOLVER.get_or_init(|| {
        let solver = WasmCvc5Solver::cvc5().expect("Failed to create global analysis solver");
        let compiler = SymCompiler::new(solver);
        Mutex::new(Some(compiler))
    }))
}

/// Analyze a Cedar `PolicySet` with respect to a given Cedar `Schema` and print the findings
pub async fn analyze_policyset(
    policy_set: PolicySet,
    schema: Schema,
) -> Result<String, ExecError> {
    let mut policy_vacuity_results = HashMap::new();
    let req_envs = OpenRequestEnv::any().to_request_envs(&schema)?;
    let policies: Vec<&Policy> = policy_set.policies().collect();

    for (i, policy) in policies.iter().enumerate() {
        let pvr = vacuity_result(policy, &schema, &req_envs).await?;
        policy_vacuity_results.insert(policy.id().clone(), pvr);
    }

    // p1 |-> [envF_1, envF_2, ..., envF_n] and p2 \in envF_i then p1 and p2 are equivalent for the ith request environment
    let mut redundant_findings: HashMap<PolicyID, Vec<HashSet<PolicyID>>> = HashMap::new();
    // p1 |-> [envF_1, envF_2, ..., envF_n] and p2 \in envF_i then p2 shadows p1 for the ith request environment
    let mut permit_shadowed_by_permit_findings: HashMap<PolicyID, Vec<HashSet<PolicyID>>> =
        HashMap::new();
    // p1 |-> [envF_1, envF_2, ..., envF_n] and p2 \in envF_i then p2 overrides p1 for the ith request environment
    let mut permit_overriden_by_forbid_findings: HashMap<PolicyID, Vec<HashSet<PolicyID>>> =
        HashMap::new();
    // p1 |-> [envF_1, envF_2, ..., envF_n] and p2 \in envF_i then p2 shadows p1 for the ith request environment
    let mut forbid_shadowed_by_forbid_findigns: HashMap<PolicyID, Vec<HashSet<PolicyID>>> =
        HashMap::new();

    let policyset_vacuity_results = policyset_vacuous(&policy_set, &schema, &req_envs).await?;

    for [src_policy, tgt_policy] in policies.iter().array_combinations() {
        let svr = policy_vacuity_results
            .get(src_policy.id())
            .expect("Vacousness of source policy not precomputed");
        let tvr = policy_vacuity_results
            .get(tgt_policy.id())
            .expect("Vacousness of target policy not precomputed");
        match (src_policy.effect(), tgt_policy.effect()) {
            (Effect::Permit, Effect::Permit) => {
                let shadowing_results = compute_permit_shadowing_result(
                    src_policy, svr, tgt_policy, tvr, &schema, &req_envs,
                ).await?;
                update_findings(
                    src_policy.id(),
                    tgt_policy.id(),
                    &shadowing_results,
                    &mut redundant_findings,
                    ShadowingResult::Equivalent,
                );
                update_findings(
                    tgt_policy.id(),
                    src_policy.id(),
                    &shadowing_results,
                    &mut redundant_findings,
                    ShadowingResult::Equivalent,
                );
                update_findings(
                    src_policy.id(),
                    tgt_policy.id(),
                    &shadowing_results,
                    &mut permit_shadowed_by_permit_findings,
                    ShadowingResult::TgtShadowsSrc,
                );
                update_findings(
                    tgt_policy.id(),
                    src_policy.id(),
                    &shadowing_results,
                    &mut permit_shadowed_by_permit_findings,
                    ShadowingResult::SrcShadowsTgt,
                );
            }
            (Effect::Permit, Effect::Forbid) => {
                let override_results = compute_forbid_overrides_shadow_result(
                    tgt_policy, tvr, src_policy, svr, &schema, &req_envs,
                ).await?;
                update_findings(
                    src_policy.id(),
                    tgt_policy.id(),
                    &override_results,
                    &mut permit_overriden_by_forbid_findings,
                    OverrideResult::Overrides,
                );
            }
            (Effect::Forbid, Effect::Permit) => {
                let override_results = compute_forbid_overrides_shadow_result(
                    src_policy, svr, tgt_policy, tvr, &schema, &req_envs,
                ).await?;
                update_findings(
                    tgt_policy.id(),
                    src_policy.id(),
                    &override_results,
                    &mut permit_overriden_by_forbid_findings,
                    OverrideResult::Overrides,
                );
            }
            (Effect::Forbid, Effect::Forbid) => {
                let shadowing_results = compute_forbid_shadowing_result(
                    src_policy, svr, tgt_policy, tvr, &schema, &req_envs,
                ).await?;
                update_findings(
                    src_policy.id(),
                    tgt_policy.id(),
                    &shadowing_results,
                    &mut redundant_findings,
                    ShadowingResult::Equivalent,
                );
                update_findings(
                    tgt_policy.id(),
                    src_policy.id(),
                    &shadowing_results,
                    &mut redundant_findings,
                    ShadowingResult::Equivalent,
                );
                update_findings(
                    src_policy.id(),
                    tgt_policy.id(),
                    &shadowing_results,
                    &mut forbid_shadowed_by_forbid_findigns,
                    ShadowingResult::TgtShadowsSrc,
                );
                update_findings(
                    tgt_policy.id(),
                    src_policy.id(),
                    &shadowing_results,
                    &mut forbid_shadowed_by_forbid_findigns,
                    ShadowingResult::SrcShadowsTgt,
                );
            }
        }
    }
    let findings = AnalyzePolicyFindings::new(
        req_envs,
        policyset_vacuity_results,
        policy_vacuity_results,
        redundant_findings,
        permit_shadowed_by_permit_findings,
        permit_overriden_by_forbid_findings,
        forbid_shadowed_by_forbid_findigns,
    );
    
    let printed_findings = findings.print_json(&policy_set);
    web_sys::console::log_2(&"Analysis findings: ".into(), &format!("{:?}", printed_findings).into());
    Ok(findings.return_json(&policy_set))
}

#[derive(Debug, Clone, Serialize)]
pub(crate) struct PerSigFindings {
    pub(crate) req_env: RequestEnvSer,
    pub(crate) equiv_classes: Vec<HashSet<PolicyID>>,
    pub(crate) permit_shadowed_by_permits: HashMap<PolicyID, HashSet<PolicyID>>,
    pub(crate) forbid_shadowed_by_forbids: HashMap<PolicyID, HashSet<PolicyID>>,
    pub(crate) permit_overriden_by_forbids: HashMap<PolicyID, HashSet<PolicyID>>,
}

impl PerSigFindings {
    pub(crate) fn new(
        req_env: RequestEnv,
        mut equiv_results: HashMap<PolicyID, HashSet<PolicyID>>,
        permit_shadowed_by_permits: HashMap<PolicyID, HashSet<PolicyID>>,
        forbid_shadowed_by_forbids: HashMap<PolicyID, HashSet<PolicyID>>,
        permit_overriden_by_forbids: HashMap<PolicyID, HashSet<PolicyID>>,
    ) -> Self {
        let mut equiv_classes = Vec::new();
        while !equiv_results.is_empty() {
            // Take first (pid, redundants) from equiv_results
            let (pid, redundants) = equiv_results
                .iter()
                .next()
                .expect("(K,V) must exist because HashMap is not empty");

            let mut equiv_class = redundants.clone();
            equiv_class.insert(pid.clone());

            for pid in equiv_class.iter() {
                equiv_results.remove(pid);
            }

            if equiv_class.len() >= 2 {
                equiv_classes.push(equiv_class);
            }
        }

        Self {
            req_env: RequestEnvSer::new(&req_env),
            equiv_classes,
            permit_shadowed_by_permits,
            forbid_shadowed_by_forbids,
            permit_overriden_by_forbids,
        }
    }

    pub fn nfindings(&self) -> usize {
        let mut ret = self.equiv_classes.len();
        for (_, s) in self.permit_shadowed_by_permits.iter() {
            ret += s.len();
        }
        for (_, s) in self.permit_overriden_by_forbids.iter() {
            ret += s.len();
        }
        for (_, s) in self.forbid_shadowed_by_forbids.iter() {
            ret += s.len();
        }
        ret
    }
}

#[derive(Debug, Clone)]
pub(crate) struct AnalyzePolicyFindings {
    pub(crate) vacuous_result: VacuityResult,
    pub(crate) vacuous_policies: HashMap<PolicyID, VacuityResult>,
    pub(crate) per_sig_findings: Vec<PerSigFindings>,
    pub(crate) req_envs: Vec<RequestEnv>,
    pub(crate) policyset_vacuity_results: Vec<VacuityResult>,
}

impl AnalyzePolicyFindings {
    pub(crate) fn new(
        req_envs: Vec<RequestEnv>,
        vacuous_results: Vec<VacuityResult>,
        policy_vacuity_results: HashMap<PolicyID, Vec<VacuityResult>>,
        redundant_findings: HashMap<PolicyID, Vec<HashSet<PolicyID>>>,
        permit_shadowed_by_permit_findings: HashMap<PolicyID, Vec<HashSet<PolicyID>>>,
        permit_overriden_by_forbid_findings: HashMap<PolicyID, Vec<HashSet<PolicyID>>>,
        forbid_shadowed_by_forbid_findigns: HashMap<PolicyID, Vec<HashSet<PolicyID>>>,
    ) -> Self {
        let req_envs_clone = req_envs.clone();
        let vacuous_results_clone = vacuous_results.clone();
        let vacuous_result = vacous_finding_from_results(&vacuous_results);
        let vacuous_policies: HashMap<PolicyID, VacuityResult> = policy_vacuity_results
            .into_iter()
            .map(|(pid, pvr)| (pid, vacous_finding_from_results(&pvr)))
            .filter(|(_, pvr)| *pvr != VacuityResult::MatchesSome)
            .collect();
        let mut per_sig_findings = Vec::new();

        for (ind, req_env) in req_envs.iter().enumerate() {
            let mut sig_redundant_findings = HashMap::new();
            for (pid, prr) in redundant_findings.iter() {
                let prs = prr
                    .get(ind)
                    .expect("Redundancy for policy not precomputed for signature");
                sig_redundant_findings.insert(pid.clone(), prs.clone());
            }

            let mut sig_permit_shadowed_findings = HashMap::new();
            for (pid, ppsr) in permit_shadowed_by_permit_findings.iter() {
                let ppss = ppsr
                    .get(ind)
                    .expect("Shadowing for policy not precomputed for signature");
                sig_permit_shadowed_findings.insert(pid.clone(), ppss.clone());
            }

            let mut sig_permit_overriden_findings = HashMap::new();
            for (pid, pofr) in permit_overriden_by_forbid_findings.iter() {
                let pofs = pofr
                    .get(ind)
                    .expect("Overriding for policy not precomputed for signature");
                sig_permit_overriden_findings.insert(pid.clone(), pofs.clone());
            }

            let mut sig_forbid_shadowed_findings = HashMap::new();
            for (pid, fsr) in forbid_shadowed_by_forbid_findigns.iter() {
                let fss = fsr
                    .get(ind)
                    .expect("Shadowing for policy not precomputed for signature");
                sig_forbid_shadowed_findings.insert(pid.clone(), fss.clone());
            }

            let sig_findings = PerSigFindings::new(
                req_env.clone(),
                sig_redundant_findings,
                sig_permit_shadowed_findings,
                sig_permit_overriden_findings,
                sig_forbid_shadowed_findings,
            );

            // if there was actually something for this signature
            if sig_findings.nfindings() != 0 {
                per_sig_findings.push(sig_findings);
            }
        }

        Self {
            vacuous_result,
            vacuous_policies,
            per_sig_findings,
            req_envs: req_envs_clone,
            policyset_vacuity_results: vacuous_results_clone,
        }
    }

    // pub fn print_table(&self) {
    //     match self.vacuous_result {
    //         VacuityResult::MatchesSome => (),
    //         VacuityResult::MatchesAll => {
    //             println!("Policyset is vacuous. Policyset allows all authorization requests.\n");
    //         }
    //         VacuityResult::MatchesNone => {
    //             println!("Policyset is vacuous. Policyset denies all authorization requests.\n");
    //         }
    //     }

    //     if !self.vacuous_policies.is_empty() {
    //         println!("Found {} vacuous policies:", self.vacuous_policies.len());

    //         for (pid, vr) in self
    //             .vacuous_policies
    //             .iter()
    //             .sorted_by_key(|(pid, _)| pid.to_string())
    //         {
    //             match vr {
    //                 VacuityResult::MatchesSome => (),
    //                 VacuityResult::MatchesAll => {
    //                     println!("Policy `{pid}` applies to all authorization requests.")
    //                 }
    //                 VacuityResult::MatchesNone => {
    //                     println!("Policy `{pid}` applies to no authorization requests.")
    //                 }
    //             }
    //         }
    //         println!()
    //     }

    //     let n_sig_findings = self
    //         .per_sig_findings
    //         .iter()
    //         .map(PerSigFindings::nfindings)
    //         .sum::<usize>();

    //     println!("Found {n_sig_findings} request environment specific warnings:");
    //     let mut table = Table::new();
    //     // Print a nice header
    //     table.add_row(Row::new(vec![
    //         Cell::new("PrincipalType").with_style(Attr::Bold),
    //         Cell::new("ActionName").with_style(Attr::Bold),
    //         Cell::new("ResourceType").with_style(Attr::Bold),
    //         Cell::new("Findings").with_style(Attr::Bold),
    //     ]));

    //     for sig_finding in self.per_sig_findings.iter() {
    //         let mut per_env_result_strs: Vec<String> = Vec::new();
    //         for equiv_class in sig_finding.equiv_classes.iter() {
    //             let result_str = format!("Redundant Policies: {}", ids_comma_sep(equiv_class));
    //             per_env_result_strs.push(result_str);
    //         }
    //         for (pid, shadowers) in sig_finding
    //             .permit_shadowed_by_permits
    //             .iter()
    //             .sorted_by_key(|(pid, _)| pid.to_string())
    //         {
    //             for spid in shadowers.iter().sorted_by_key(|pid| pid.to_string()) {
    //                 let result_str = format!("Policy `{pid}` shadowed by `{spid}`");
    //                 per_env_result_strs.push(result_str);
    //             }
    //         }
    //         for (pid, overriders) in sig_finding
    //             .permit_overriden_by_forbids
    //             .iter()
    //             .sorted_by_key(|(pid, _)| pid.to_string())
    //         {
    //             for opid in overriders.iter().sorted_by_key(|pid| pid.to_string()) {
    //                 let result_str = format!("Policy `{pid}` overriden by `{opid}`");
    //                 per_env_result_strs.push(result_str);
    //             }
    //         }
    //         for (pid, shadowers) in sig_finding
    //             .forbid_shadowed_by_forbids
    //             .iter()
    //             .sorted_by_key(|(pid, _)| pid.to_string())
    //         {
    //             for spid in shadowers.iter().sorted_by_key(|pid| pid.to_string()) {
    //                 let result_str = format!("Policy `{pid}` shadowed by `{spid}`");
    //                 per_env_result_strs.push(result_str);
    //             }
    //         }
    //         table.add_row(Row::new(vec![
    //             Cell::new(&sig_finding.req_env.principal_type),
    //             Cell::new(&sig_finding.req_env.action_uid),
    //             Cell::new(&sig_finding.req_env.resource_type),
    //             Cell::new(&per_env_result_strs.join("\n")),
    //         ]));
    //     }
    //     table.printstd();
    // }

    pub fn print_json(&self, policy_set: &PolicySet) {
        let serializable_findings = AnalyzePolicyFindingsSer::new(self, policy_set);
        let json = serde_json::to_string_pretty(&serializable_findings).unwrap();
        println!("{}", json);
    }
    pub fn return_json(&self, policy_set: &PolicySet) -> String {
        let logical_errors = LogicalErrorFindings::from_analysis(self, policy_set);
        serde_json::to_string_pretty(&logical_errors).unwrap()
    }
}

fn ids_comma_sep(pids: &HashSet<PolicyID>) -> String {
    let mut ret = "".into();
    for (ind, pid) in pids.iter().sorted_by_key(|pid| pid.to_string()).enumerate() {
        if ind == 0 {
            ret = format!("`{pid}`");
        } else if pids.len() == 2 {
            ret = format!("{ret} and `{pid}`");
        } else if ind + 1 != pids.len() {
            ret = format!("{ret}, `{pid}`");
        } else {
            ret = format!("`{ret}`, and `{pid}`")
        }
    }
    ret
}

#[derive(Debug, Serialize)]
struct LogicalErrorFindings {
    permit_shadows_permit: PermitShadowsPermitSummary,
    permit_allows_none: ErrorSummary,
    forbid_overrides_permit: ForbidOverridesPermitSummary,
    equivalent_permits: EquivalentPermitsSummary,
    policy_set_denies_all: PolicySetDeniesAllSummary,
}

#[derive(Debug, Serialize)]
struct ErrorSummary {
    count: usize,
    policies: Vec<PolicyError>,
}

#[derive(Debug, Serialize)]
struct PermitShadowsPermitSummary {
    count: usize,
    shadowed_policies: Vec<PolicyError>,
    shadowing_policies: Vec<PolicyError>,
}

#[derive(Debug, Serialize)]
struct ForbidOverridesPermitSummary {
    count: usize,
    permit_policies: Vec<PolicyError>,
    forbid_policies: Vec<PolicyError>,
}

#[derive(Debug, Serialize)]
struct EquivalentPermitsSummary {
    count: usize,
    first_policies: Vec<PolicyError>,
    second_policies: Vec<PolicyError>,
}

#[derive(Debug, Serialize)]
struct PolicySetDeniesAllSummary {
    count: usize,
    signatures: Vec<PolicySetDeniesAllError>,
}

#[derive(Debug, Serialize, Clone)]
struct PolicyError {
    policy_id: String,
    policy_text: String,
}

#[derive(Debug, Serialize)]
struct PolicySetDeniesAllError {
    principal_type: String,
    action_uid: String,
    resource_type: String,
}

impl LogicalErrorFindings {
    fn from_analysis(findings: &AnalyzePolicyFindings, policy_set: &PolicySet) -> Self {
        let mut shadowed_policies = Vec::new();
        let mut shadowing_policies = Vec::new();
        let mut permit_allows_none = Vec::new();
        let mut permit_policies = Vec::new();
        let mut forbid_policies = Vec::new();
        let mut first_equivalent_policies = Vec::new();
        let mut second_equivalent_policies = Vec::new();
        let mut policy_set_denies_all_sigs = Vec::new();
        
        // Check for policy set denies all 
        if findings.vacuous_result == VacuityResult::MatchesNone {
            // Add all request environments where the policy set denies all
            for req_env in &findings.req_envs {
                policy_set_denies_all_sigs.push(PolicySetDeniesAllError {
                    principal_type: req_env.principal().to_string(),
                    action_uid: req_env.action().to_string(),
                    resource_type: req_env.resource().to_string(),
                });
            }
        }
        
        // Check for permit allows none 
        for (pid, vr) in &findings.vacuous_policies {
            if let Some(policy) = policy_set.all_templates().find(|p| p.id() == pid) {
                if policy.effect() == Effect::Permit && *vr == VacuityResult::MatchesNone {
                    permit_allows_none.push(PolicyError {
                        policy_id: pid.to_string(),
                        policy_text: policy.to_string(),
                    });
                }
            }
        }
        
        // Process per-signature findings 
        for sig_finding in &findings.per_sig_findings {
            // Equivalent permits (redundant policies)
            for equiv_class in &sig_finding.equiv_classes {
                let policies: Vec<_> = equiv_class.iter().filter_map(|pid| {
                    policy_set.all_templates().find(|p| p.id() == pid).map(|policy| PolicyError {
                        policy_id: pid.to_string(),
                        policy_text: policy.to_string(),
                    })
                }).collect();
                
                if policies.len() >= 2 {
                    first_equivalent_policies.push(policies[0].clone());
                    second_equivalent_policies.push(policies[1].clone());
                }
            }
            
            // Permit shadows permit
            for (pid, shadowers) in &sig_finding.permit_shadowed_by_permits {
                // Add the shadowed policy
                if let Some(policy) = policy_set.all_templates().find(|p| p.id() == pid) {
                    shadowed_policies.push(PolicyError {
                        policy_id: pid.to_string(),
                        policy_text: policy.to_string(),
                    });
                }
                // Add the shadowing policies (first one corresponds to the shadowed policy above)
                if let Some(first_shadower) = shadowers.iter().next() {
                    if let Some(policy) = policy_set.all_templates().find(|p| p.id() == first_shadower) {
                        shadowing_policies.push(PolicyError {
                            policy_id: first_shadower.to_string(),
                            policy_text: policy.to_string(),
                        });
                    }
                }
            }
            
            // Forbid overrides permit
            for (pid, overriders) in &sig_finding.permit_overriden_by_forbids {
                // Add the overridden permit policy
                if let Some(policy) = policy_set.all_templates().find(|p| p.id() == pid) {
                    permit_policies.push(PolicyError {
                        policy_id: pid.to_string(),
                        policy_text: policy.to_string(),
                    });
                }
                // Add the overriding forbid policies (first one corresponds to the permit policy above)
                if let Some(first_overrider) = overriders.iter().next() {
                    if let Some(policy) = policy_set.all_templates().find(|p| p.id() == first_overrider) {
                        forbid_policies.push(PolicyError {
                            policy_id: first_overrider.to_string(),
                            policy_text: policy.to_string(),
                        });
                    }
                }
            }
        }
        
        Self {
            permit_shadows_permit: PermitShadowsPermitSummary { 
                count: shadowed_policies.len(), 
                shadowed_policies, 
                shadowing_policies 
            },
            permit_allows_none: ErrorSummary { count: permit_allows_none.len(), policies: permit_allows_none },
            forbid_overrides_permit: ForbidOverridesPermitSummary { 
                count: permit_policies.len(), 
                permit_policies, 
                forbid_policies 
            },
            equivalent_permits: EquivalentPermitsSummary { 
                count: first_equivalent_policies.len(), 
                first_policies: first_equivalent_policies, 
                second_policies: second_equivalent_policies 
            },
            policy_set_denies_all: PolicySetDeniesAllSummary { count: policy_set_denies_all_sigs.len(), signatures: policy_set_denies_all_sigs },
        }
    }
}

#[allow(clippy::enum_variant_names)]
/// A policy can be non-vacuous (MatchesSome) or vacuous by applying to all requests (MatchesAll) or no requests (MatchesNone)
#[derive(Clone, Copy, Debug, PartialEq, Serialize)]
pub enum VacuityResult {
    MatchesAll,
    MatchesSome,
    MatchesNone,
}

fn vacous_finding_from_results(results: &[VacuityResult]) -> VacuityResult {
    if results.iter().all(|res| *res == VacuityResult::MatchesAll) {
        VacuityResult::MatchesAll
    } else if results.iter().all(|res| *res == VacuityResult::MatchesNone) {
        VacuityResult::MatchesNone
    } else {
        VacuityResult::MatchesSome
    }
}

/// Is a given PolicySet vacous (per request environment)
async fn policyset_vacuous(
    policyset: &cedar_policy_core::ast::PolicySet,
    schema: &Schema,
    req_envs: &Vec<RequestEnv>,
) -> Result<Vec<VacuityResult>, ExecError> {
    let mut vr = Vec::new();

    let compiler_mutex = get_global_analysis_compiler()?;
    let mut compiler_guard = compiler_mutex.lock().unwrap();
    let sym_compiler = compiler_guard.as_mut().unwrap();
    
    for req_env in req_envs {
        let symenv = SymEnv::new(schema, req_env)
            .map_err(|e| ExecError::Other(format!("Failed to create symbolic environment: {}", e)))?;
        let always_allows = sym_compiler.check_always_allows(&policyset, &symenv)
            .await
            .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;
        if always_allows {
            vr.push(VacuityResult::MatchesAll);
        } else  {
            let always_denies = sym_compiler.check_always_denies(&policyset, &symenv)
                .await
                .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;
            if always_denies {
                vr.push(VacuityResult::MatchesNone);
            } else {
                vr.push(VacuityResult::MatchesSome);
            }
        }
    }
    Ok(vr)
}

/// Auxillary function that computes the vacuitiness of a policy for each request environment
async fn vacuity_result(
    policy: &Policy,
    schema: &Schema,
    req_envs: &Vec<RequestEnv>,
) -> Result<Vec<VacuityResult>, ExecError> {
    // turn forbid to permit to test if policy matches All, Some, or No requests
    // by checking if the permit variant allows All, None, or Some
    let permit_policy = force_permit(policy)?;

    let mut pset = cedar_policy_core::ast::PolicySet::new();
    let _ = pset.add(permit_policy.clone()).map_err(|err| {
        ExecError::PolicyIntoPolicySetError {
            error: Box::new(err),
        }
    });

    policyset_vacuous(&pset, schema, req_envs).await
}

/// Represents if the Src Policy is shadowed by the Tgt Policy or vice versa
#[derive(Clone, Copy, Debug, PartialEq)]
enum ShadowingResult {
    Equivalent,    // Src & Tgt are non vacuous and allow the same requests
    SrcShadowsTgt, // Src & Tgt are non vacuous and Src allows strictly more requests than Tgt
    TgtShadowsSrc, // Src & Tgt are non vacuous and Tgt allows strictly more requests than Src
    NoResult,      // Either Src or Tgt is vacuous or allow incomporable sets of requests
}

/// Compute Redudant and Shadowed relationship between src and tgt policies (per environment)
async fn compute_permit_shadowing_result(
    src_policy: &Policy,
    src_vacuous_results: &Vec<VacuityResult>,
    tgt_policy: &Policy,
    tgt_vacuous_results: &Vec<VacuityResult>,
    schema: &Schema,
    req_envs: &Vec<RequestEnv>,
) -> Result<Vec<ShadowingResult>, ExecError> {
    let mut results = Vec::new();
    
    let mut src_pset = cedar_policy_core::ast::PolicySet::new();
    src_pset.add(src_policy.clone()).map_err(|err| {
        ExecError::PolicyIntoPolicySetError {
            error: Box::new(err),
        }
    })?;
    
    let mut tgt_pset = cedar_policy_core::ast::PolicySet::new();
    tgt_pset.add(tgt_policy.clone()).map_err(|err| {
        ExecError::PolicyIntoPolicySetError {
            error: Box::new(err),
        }
    })?;

    // Use global compiler for symbolic analysis
    let compiler_mutex = get_global_analysis_compiler()?;
    let mut compiler_guard = compiler_mutex.lock().unwrap();
    let sym_compiler = compiler_guard.as_mut().unwrap();
    
    for ((src_vr, tgt_vr), req_env) in zip(zip(src_vacuous_results, tgt_vacuous_results), req_envs)
    {
        match (src_vr, tgt_vr) {
            (VacuityResult::MatchesNone, _) | (_, VacuityResult::MatchesNone) => {
                results.push(ShadowingResult::NoResult)
            }
            (VacuityResult::MatchesAll, VacuityResult::MatchesAll) => {
                results.push(ShadowingResult::Equivalent)
            }
            (VacuityResult::MatchesAll, VacuityResult::MatchesSome) => {
                results.push(ShadowingResult::SrcShadowsTgt)
            }
            (VacuityResult::MatchesSome, VacuityResult::MatchesAll) => {
                results.push(ShadowingResult::TgtShadowsSrc)
            }
            (VacuityResult::MatchesSome, VacuityResult::MatchesSome) => {
                // Create symbolic environment
                let symenv = SymEnv::new(schema, req_env)
                    .map_err(|e| ExecError::Other(format!("Failed to create symbolic environment: {}", e)))?;
                
                // Check if src implies tgt
                let src_implies_tgt = sym_compiler.check_implies(&src_pset, &tgt_pset, &symenv)
                    .await
                    .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;
                
                // Check if tgt implies src
                let tgt_implies_src = sym_compiler.check_implies(&tgt_pset, &src_pset, &symenv)
                    .await
                    .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;
                
                match (src_implies_tgt, tgt_implies_src) {
                    (true, true) => results.push(ShadowingResult::Equivalent),
                    (true, _) => results.push(ShadowingResult::TgtShadowsSrc),
                    (_, true) => results.push(ShadowingResult::SrcShadowsTgt),
                    (_, _) => results.push(ShadowingResult::NoResult),
                }
            }
        }
    }
    Ok(results)
}


/// Represents if the Forbid policy overrides the Permit policy
#[derive(Clone, Copy, Debug, PartialEq)]
enum OverrideResult {
    Overrides, // Forbid policy overrides Permit policy
    NoResult, // Either the Forbid or Permit policy is vacuous or there is a request allowed by the Permit policy that is not forbidden by the Forbid policy
}

/// Determine if forbid policy overrides permit policy (per environment)
async fn compute_forbid_overrides_shadow_result(
    forbid_policy: &Policy,
    forbid_vacuous_results: &Vec<VacuityResult>,
    permit_policy: &Policy,
    permit_vacuous_results: &Vec<VacuityResult>,
    schema: &Schema,
    req_envs: &Vec<RequestEnv>,
) -> Result<Vec<OverrideResult>, ExecError> {
    let mut results = Vec::new();

    let mut forbid_pset = cedar_policy_core::ast::PolicySet::new();
    let _ = forbid_pset.add(force_permit(forbid_policy)?).map_err(|err| {
        ExecError::PolicyIntoPolicySetError {
            error: Box::new(err),
        }
    });

    let mut permit_pset = cedar_policy_core::ast::PolicySet::new();
    let _ = permit_pset.add(permit_policy.clone()).map_err(|err| {
        ExecError::PolicyIntoPolicySetError {
            error: Box::new(err),
        }
    });

    let compiler_mutex = get_global_analysis_compiler()?;
    let mut compiler_guard = compiler_mutex.lock().unwrap();
    let sym_compiler = compiler_guard.as_mut().unwrap();

    for ((forbid_vr, permit_vr), req_env) in zip(
        zip(forbid_vacuous_results, permit_vacuous_results),
        req_envs,
    ) {
        match (forbid_vr, permit_vr) {
            (VacuityResult::MatchesNone, _) | (VacuityResult::MatchesAll, _) |                                          // forbid policy is vacous: does not apply or denies all
            (_, VacuityResult::MatchesNone) | (_, VacuityResult::MatchesAll) => results.push(OverrideResult::NoResult), // permit policy is vacous: does not apply or allows all (no need to check overriding)
            _ => {
                let symenv = SymEnv::new(schema, req_env)
                    .map_err(|e| ExecError::Other(format!("Failed to create symbolic environment: {}", e)))?;
                let check_implies = sym_compiler.check_implies(&permit_pset, &forbid_pset, &symenv)
                    .await
                    .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;
                if check_implies {
                    results.push(OverrideResult::Overrides); // Every request allowed by permit is denied by forbid
                } else {
                    results.push(OverrideResult::NoResult);  // some request allowed by permit is not denies by forbid
                }
            }
        }
    }
    Ok(results)
}

/// Compute Shadoing (and redudancy) relationship between src and tgt policies (per request environment)
async fn compute_forbid_shadowing_result(
    src_policy: &Policy,
    src_vacuous_results: &Vec<VacuityResult>,
    tgt_policy: &Policy,
    tgt_vacuous_results: &Vec<VacuityResult>,
    schema: &Schema,
    req_envs: &Vec<RequestEnv>,
) -> Result<Vec<ShadowingResult>, ExecError> {
    let mut results = Vec::new();

    let mut src_pset = cedar_policy_core::ast::PolicySet::new();
    let _ = src_pset.add(force_permit(src_policy)?).map_err(|err| {
        ExecError::PolicyIntoPolicySetError {
            error: Box::new(err),
        }
    });

    let mut tgt_pset = cedar_policy_core::ast::PolicySet::new();
    let _ = tgt_pset.add(force_permit(tgt_policy)?).map_err(|err| {
        ExecError::PolicyIntoPolicySetError {
            error: Box::new(err),
        }
    });

    let compiler_mutex = get_global_analysis_compiler()?;
    let mut compiler_guard = compiler_mutex.lock().unwrap();
    let sym_compiler = compiler_guard.as_mut().unwrap();

    for ((src_vr, tgt_vr), req_env) in zip(zip(src_vacuous_results, tgt_vacuous_results), req_envs)
    {
        let symenv = SymEnv::new(schema, req_env)
            .map_err(|e| ExecError::Other(format!("Failed to create symbolic environment: {}", e)))?;
        // Forbid vacuity results are computed on them as if they were permit policies
        match (src_vr, tgt_vr) {
            (VacuityResult::MatchesNone, _) | (_, VacuityResult::MatchesNone) => {
                results.push(ShadowingResult::NoResult) // One of the two policies is vacuous
            }
            (VacuityResult::MatchesAll, VacuityResult::MatchesAll) => {
                results.push(ShadowingResult::Equivalent) // Both policies deny all requests
            }
            (VacuityResult::MatchesAll, VacuityResult::MatchesSome) => {
                results.push(ShadowingResult::SrcShadowsTgt) // Src policy denies all requests, Tgt denies some
            }
            (VacuityResult::MatchesSome, VacuityResult::MatchesAll) => {
                results.push(ShadowingResult::TgtShadowsSrc) // Tgt policy denies all requests, Src denies some
            }
            (VacuityResult::MatchesSome, VacuityResult::MatchesSome) => {
                let src_implies_tgt = sym_compiler.check_implies(&src_pset, &tgt_pset, &symenv)
                    .await
                    .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;
                
                let tgt_implies_src = sym_compiler.check_implies(&tgt_pset, &src_pset, &symenv)
                    .await
                    .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;
                match (src_implies_tgt, tgt_implies_src) {
                    (true, true) => results.push(ShadowingResult::Equivalent), // Equivalent
                    (true, _) => results.push(ShadowingResult::TgtShadowsSrc), // Tgt denies strictly more than Src
                    (_, true) => results.push(ShadowingResult::SrcShadowsTgt), // Src denies strictly more than Tgt
                    (_, _) => results.push(ShadowingResult::NoResult),         // Incomparable
                }
            }
        }
    }
    Ok(results)
}

/// Converts a forbid policy into a permit policy
fn force_permit(policy: &Policy) -> Result<Policy, ExecError> {
    use cedar_policy_core::ast::{Effect};
    
    // Create a new policy with the same ID, conditions, but with PERMIT effect
    let new_policy = Policy::from_when_clause(
        Effect::Permit,
        policy.condition().clone(),
        policy.id().clone(),
        policy.loc().cloned(),
    );
    
    Ok(new_policy)
}

/// if results[j] == result_filter then update the findings such that tgt_pid \in envF_i where src_pid |-> [envF_1, ..., envF_n]
fn update_findings<T>(
    src_pid: &PolicyID,
    tgt_pid: &PolicyID,
    results: &[T],
    findings: &mut HashMap<PolicyID, Vec<HashSet<PolicyID>>>,
    result_filter: T,
) where
    T: PartialEq,
{
    if !findings.contains_key(src_pid) {
        findings.insert(src_pid.clone(), vec![HashSet::new(); results.len()]);
    }
    let src_findings = findings
        .get_mut(src_pid)
        .expect("Findings are unexpectedly missing");
    for (ind, result) in results.iter().enumerate() {
        if *result == result_filter {
            src_findings[ind].insert(tgt_pid.clone());
        }
    }
}

#[derive(Debug, Clone, Serialize)]
enum PolicySetComparisonStatus {
    MorePermissive,
    LessPermissive,
    Equivalent,
    Incomparable,
}

impl PolicySetComparisonStatus {
    fn print(self) -> String {
        match self {
            PolicySetComparisonStatus::MorePermissive => {
                String::from("Source PolicySet is more permissive than Target Policy")
            }
            PolicySetComparisonStatus::LessPermissive => {
                String::from("Source PolicySet is less permissive than Target Policy")
            }
            PolicySetComparisonStatus::Equivalent => {
                String::from("Source PolicySet is equivalent to Target Policy")
            }
            PolicySetComparisonStatus::Incomparable => {
                String::from("Source PolicySet is incomparable with Target Policy")
            }
        }
    }
}

#[derive(Debug, Serialize)]
struct PolicySetComparisonResult {
    req_env: RequestEnvSer,
    status: PolicySetComparisonStatus,
}

// fn print_compare_results(results: &[PolicySetComparisonResult]) {
//     let mut table = Table::new();
//     // Print a nice header
//     table.add_row(Row::new(vec![
//         Cell::new("PrincipalType").with_style(Attr::Bold),
//         Cell::new("ActionName").with_style(Attr::Bold),
//         Cell::new("ResourceType").with_style(Attr::Bold),
//         Cell::new("Result").with_style(Attr::Bold),
//     ]));

//     for res in results.iter() {
//         table.add_row(Row::new(vec![
//             Cell::new(&res.req_env.principal_type),
//             Cell::new(&res.req_env.action_uid),
//             Cell::new(&res.req_env.resource_type),
//             Cell::new(&res.status.clone().print()),
//         ]));
//     }
//     table.printstd();
// }
/// Compare src policyset to tgt policyset and print results
pub async fn compare_policysets(
    src_policyset: PolicySet,
    tgt_policyset: PolicySet,
    schema: Schema,
) -> Result<String, ExecError> {
    let req_envs = OpenRequestEnv::any().to_request_envs(&schema)?;
    let compiler_mutex = get_global_analysis_compiler()?;
    let mut compiler_guard = compiler_mutex.lock().unwrap();
    let sym_compiler = compiler_guard.as_mut().unwrap();

    // Create a vector to store the results
    let mut comparison_results = Vec::new();
    
    // Process each request environment sequentially
    for req_env in req_envs.iter() {
        let symenv = SymEnv::new(&schema, req_env)
            .map_err(|e| ExecError::Other(format!("Failed to create symbolic environment: {}", e)))?;

        let fwd_implies = sym_compiler.check_implies(&src_policyset, &tgt_policyset, &symenv)
            .await
            .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;

        let bwd_implies = sym_compiler.check_implies(&tgt_policyset, &src_policyset, &symenv)
            .await
            .map_err(|e| ExecError::Other(format!("SymCC error: {}", e)))?;
        
        let status = match (fwd_implies, bwd_implies) {
            (true, true) => PolicySetComparisonStatus::Equivalent,
            (true, false) => PolicySetComparisonStatus::LessPermissive,
            (false, true) => PolicySetComparisonStatus::MorePermissive,
            (false, false) => PolicySetComparisonStatus::Incomparable,
        };
        
        comparison_results.push(PolicySetComparisonResult {
            req_env: RequestEnvSer::new(req_env),
            status,
        });
    }
    let json = serde_json::to_string_pretty(&comparison_results).unwrap();
    Ok(json)
}

