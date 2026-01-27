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
use crate::err::ExecError;
use crate::util::{OpenRequestEnv, ReqEnv};
use cedar_lean_ffi::CedarLeanFfi;
use cedar_policy::{Policy, PolicySet, RequestEnv, Schema};
use std::iter::zip;

/// Run lean backend for analysis `check-never-errors`
pub fn run_check_never_errors(
    policy: Policy,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    let mut results = Vec::new();
    for req_env in req_envs.iter() {
        results.push(lean_context.run_check_never_errors(&policy, schema.clone(), req_env)?);
    }
    print_check_never_errors_results(&results, &req_envs, request_env);
    Ok(())
}

/// Run lean backend for analysis `check-always-allows`
pub fn run_check_always_allows(
    policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    let mut results = Vec::new();
    for req_env in req_envs.iter() {
        results.push(lean_context.run_check_always_allows(&policyset, schema.clone(), req_env)?);
    }
    print_check_always_allows_results(&results, &req_envs, request_env);
    Ok(())
}

/// Run lean backend for analysis `check-always-denies`
pub fn run_check_always_denies(
    policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    let mut results = Vec::new();
    for req_env in req_envs.iter() {
        results.push(lean_context.run_check_always_denies(&policyset, schema.clone(), req_env)?);
    }
    print_check_always_denies_results(&results, &req_envs, request_env);
    Ok(())
}

/// Run lean backend for analysis `check-equivalent`
pub fn run_check_equivalent(
    src_policyset: PolicySet,
    tgt_policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    let mut results = Vec::new();
    for req_env in req_envs.iter() {
        results.push(lean_context.run_check_equivalent(
            &src_policyset,
            &tgt_policyset,
            schema.clone(),
            req_env,
        )?);
    }
    print_check_equivalent_results(&results, &req_envs, request_env);
    Ok(())
}

/// Run lean backend for analysis `check-implies`
/// Checks if Src => Tgt---i.e., If every request allowed by src is also allowed by tgt
pub fn run_check_implies(
    src_policyset: PolicySet,
    tgt_policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    let mut results = Vec::new();
    for req_env in req_envs.iter() {
        results.push(lean_context.run_check_implies(
            &src_policyset,
            &tgt_policyset,
            schema.clone(),
            req_env,
        )?);
    }
    print_check_implies_results(&results, &req_envs, request_env);
    Ok(())
}
/// Run lean backend for analysis `check-denies`
pub fn run_check_disjoint(
    src_policyset: PolicySet,
    tgt_policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    let mut results = Vec::new();
    for req_env in req_envs.iter() {
        results.push(lean_context.run_check_disjoint(
            &src_policyset,
            &tgt_policyset,
            schema.clone(),
            req_env,
        )?);
    }
    print_check_disjoint_results(&results, &req_envs, request_env);
    Ok(())
}

/// Prints to stdout the SMTLib script produced by the lean backend for analysis `check-never-errors`
pub fn print_check_never_errors(
    policy: Policy,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    for req_env in req_envs {
        println!(";;");
        println!(
            ";; SMTLib encoding for RequestEnv {}",
            ReqEnv::Env(req_env.clone())
        );
        println!(";;");
        lean_context.print_check_never_errors(&policy, schema.clone(), &req_env)?;
        println!();
    }
    Ok(())
}

/// Prints to stdout the SMTLib script produced by the lean backend for analysis `check-always-allows`
pub fn print_check_always_allows(
    policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    for req_env in req_envs {
        println!(";;");
        println!(
            ";; SMTLib encoding for RequestEnv {}",
            ReqEnv::Env(req_env.clone())
        );
        println!(";;");
        lean_context.print_check_always_allows(&policyset, schema.clone(), &req_env)?;
        println!();
    }
    Ok(())
}

/// Prints to stdout the SMTLib script produced by the lean backend for analysis `check-always-denies`
pub fn print_check_always_denies(
    policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    for req_env in req_envs {
        println!(";;");
        println!(
            ";; SMTLib encoding for RequestEnv {}",
            ReqEnv::Env(req_env.clone())
        );
        println!(";;");
        lean_context.print_check_always_denies(&policyset, schema.clone(), &req_env)?;
        println!();
    }
    Ok(())
}

/// Prints to stdout the SMTLib script produced by the lean backend for analysis `check-equivalent`
pub fn print_check_equivalent(
    src_policyset: PolicySet,
    tgt_policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    for req_env in req_envs {
        println!(";;");
        println!(
            ";; SMTLib encoding for RequestEnv {}",
            ReqEnv::Env(req_env.clone())
        );
        println!(";;");
        lean_context.print_check_equivalent(
            &src_policyset,
            &tgt_policyset,
            schema.clone(),
            &req_env,
        )?;
        println!();
    }
    Ok(())
}

/// Prints to stdout the SMTLib script produced by the lean backend for analysis `check-implies`
pub fn print_check_implies(
    src_policyset: PolicySet,
    tgt_policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    for req_env in req_envs {
        println!(";;");
        println!(
            ";; SMTLib encoding for RequestEnv {}",
            ReqEnv::Env(req_env.clone())
        );
        println!(";;");
        lean_context.print_check_implies(
            &src_policyset,
            &tgt_policyset,
            schema.clone(),
            &req_env,
        )?;
        println!();
    }
    Ok(())
}

/// Prints to stdout the SMTLib script produced by the lean backend for analysis `check-disjoint`
pub fn print_check_disjoint(
    src_policyset: PolicySet,
    tgt_policyset: PolicySet,
    schema: Schema,
    request_env: &OpenRequestEnv,
) -> Result<(), ExecError> {
    let lean_context = CedarLeanFfi::new();
    let req_envs = request_env.to_request_envs(&schema)?;
    let schema = lean_context.load_lean_schema_object(&schema)?;
    for req_env in req_envs {
        println!(";;");
        println!(
            ";; SMTLib encoding for RequestEnv {}",
            ReqEnv::Env(req_env.clone())
        );
        println!(";;");
        lean_context.print_check_disjoint(
            &src_policyset,
            &tgt_policyset,
            schema.clone(),
            &req_env,
        )?;
        println!();
    }
    Ok(())
}

/***************************************************************************************************
 * Functions to pretty print results
 ***************************************************************************************************/

struct SigWidths {
    principal_width: usize,
    action_width: usize,
    resource_width: usize,
}

impl SigWidths {
    pub fn from_req_envs(req_envs: &[RequestEnv]) -> Self {
        let mut principal_width = 13; // PrincipalType
        let mut action_width = 10; // ActionName
        let mut resource_width = 12; // ResourceType

        for req_env in req_envs.iter() {
            principal_width = std::cmp::max(principal_width, req_env.principal().basename().len());
            action_width = std::cmp::max(action_width, req_env.action().id().escaped().len());
            resource_width = std::cmp::max(resource_width, req_env.resource().basename().len());
        }

        Self {
            principal_width,
            action_width,
            resource_width,
        }
    }

    pub fn principal(&self) -> usize {
        self.principal_width
    }

    pub fn action(&self) -> usize {
        self.action_width
    }

    pub fn resource(&self) -> usize {
        self.resource_width
    }

    pub fn print_header(&self, result_width: usize, result_name: &str) {
        let table_width = 13 + self.principal() + self.action() + self.resource() + result_width; // | {principal} | {action} | {resource} | {result} |
        println!("{:=^1$}", "", table_width);
        print!("| {: ^1$} | ", "PrincipalType", self.principal());
        print!("{: ^1$} | ", "ActionName", self.action());
        print!("{: ^1$} | ", "ResourceType", self.resource());
        println!("{: ^1$} |", result_name, result_width);
        println!("{:-^1$}", "", table_width);
    }

    pub fn print_row(&self, req_env: &RequestEnv, result_width: usize, result: &str) {
        print!(
            "| {: ^1$} | ",
            req_env.principal().basename(),
            self.principal()
        );
        print!("{: ^1$} | ", req_env.action().id().escaped(), self.action());
        print!("{: ^1$} | ", req_env.resource().basename(), self.resource());
        println!("{: ^1$} |", result, result_width);
    }

    pub fn print_footer(&self, result_width: usize) {
        let table_width = 13 + self.principal() + self.action() + self.resource() + result_width; // | {principal} | {action} | {resource} | {result} |
        println!("{:=^1$}", "", table_width);
    }
}

fn print_check_never_errors_results(
    results: &[bool],
    req_envs: &[RequestEnv],
    open_req_env: &OpenRequestEnv,
) {
    if results.iter().all(|r| *r) {
        if open_req_env.is_any() {
            println!("Policy never errors")
        } else {
            println!("Policy never errors when {}", open_req_env)
        }
    } else if results.iter().all(|r| !*r) {
        if open_req_env.is_any() {
            println!("Policy can error for all request signatures")
        } else {
            println!(
                "Policy can error for all request signatures where {}",
                open_req_env
            )
        }
    } else if open_req_env.is_any() {
        println!("Policy can error for some request signatures")
    } else {
        println!(
            "Policy can error for some request signatures where {}",
            open_req_env
        )
    }

    println!();
    println!("Per request signature results:");

    let sig_widths = SigWidths::from_req_envs(req_envs);
    let res_width = 12; // Never Errors

    sig_widths.print_header(res_width, "Result");
    for (req_env, result) in zip(req_envs.iter(), results.iter()) {
        let result = if *result { "Never Errors" } else { "Errors" };
        sig_widths.print_row(req_env, res_width, result);
    }
    sig_widths.print_footer(res_width);
}

fn print_check_always_allows_results(
    results: &[bool],
    req_envs: &[RequestEnv],
    open_req_env: &OpenRequestEnv,
) {
    if results.iter().all(|r| *r) {
        if open_req_env.is_any() {
            println!("PolicySet allows all requests")
        } else {
            println!("PolicySet allows all requests when {}", open_req_env)
        }
    } else if results.iter().all(|r| !*r) {
        if open_req_env.is_any() {
            println!("PolicySet does not allow all requests for all request signatures")
        } else {
            println!(
                "PolicySet does not allow all requests when {}",
                open_req_env
            )
        }
    } else if open_req_env.is_any() {
        println!("PolicySet allows all requests for some request signatures")
    } else {
        println!(
            "PolicySet allows all requests for some request signatures where {}",
            open_req_env
        )
    }

    println!();
    println!("Per request signature results:");

    let sig_widths = SigWidths::from_req_envs(req_envs);
    let res_width = 18; // Does not Allow All

    sig_widths.print_header(res_width, "Result");
    for (req_env, result) in zip(req_envs.iter(), results.iter()) {
        let result = if *result {
            "Allows All"
        } else {
            "Does not Allow All"
        };
        sig_widths.print_row(req_env, res_width, result);
    }
    sig_widths.print_footer(res_width);
}

fn print_check_always_denies_results(
    results: &[bool],
    req_envs: &[RequestEnv],
    open_req_env: &OpenRequestEnv,
) {
    if results.iter().all(|r| *r) {
        if open_req_env.is_any() {
            println!("PolicySet denies all requests")
        } else {
            println!("PolicySet denies all requests when {}", open_req_env)
        }
    } else if results.iter().all(|r| !*r) {
        if open_req_env.is_any() {
            println!("PolicySet does not deny all requests for all request signatures")
        } else {
            println!("PolicySet does not deny all requests when {}", open_req_env)
        }
    } else if open_req_env.is_any() {
        println!("PolicySet denies all requests for some request signatures")
    } else {
        println!(
            "PolicySet denies all requests for some request signatures where {}",
            open_req_env
        )
    }

    println!();
    println!("Per request signature results:");

    let sig_widths = SigWidths::from_req_envs(req_envs);
    let res_width = 17; // Does not Deny All

    sig_widths.print_header(res_width, "Result");
    for (req_env, result) in zip(req_envs.iter(), results.iter()) {
        let result = if *result {
            "Denies All"
        } else {
            "Does not Deny All"
        };
        sig_widths.print_row(req_env, res_width, result);
    }
    sig_widths.print_footer(res_width);
}

fn print_check_equivalent_results(
    results: &[bool],
    req_envs: &[RequestEnv],
    open_req_env: &OpenRequestEnv,
) {
    if results.iter().all(|r| *r) {
        if open_req_env.is_any() {
            println!("Source and Target PolicySets are equivalent")
        } else {
            println!(
                "Source and Target PolicySets are equivalent when {}",
                open_req_env
            )
        }
    } else if results.iter().all(|r| !*r) {
        if open_req_env.is_any() {
            println!("Source and Target PolicySets are not equivalent")
        } else {
            println!(
                "Source and Target PolicySets are not equivalent for all requests when {}",
                open_req_env
            )
        }
    } else if open_req_env.is_any() {
        println!("Source and Target PolicySets are not equivalent for some signatures")
    } else {
        println!(
            "Source and Target PolicySets are not equivalent for some request signatures where {}",
            open_req_env
        )
    }

    println!();
    println!("Per request signature results:");

    let sig_widths = SigWidths::from_req_envs(req_envs);
    let res_width = 14; // Not Equivalent

    sig_widths.print_header(res_width, "Result");
    for (req_env, result) in zip(req_envs.iter(), results.iter()) {
        let result = if *result {
            "Equivalent"
        } else {
            "Not Equivalent"
        };
        sig_widths.print_row(req_env, res_width, result);
    }
    sig_widths.print_footer(res_width);
}

fn print_check_implies_results(
    results: &[bool],
    req_envs: &[RequestEnv],
    open_req_env: &OpenRequestEnv,
) {
    if results.iter().all(|r| *r) {
        if open_req_env.is_any() {
            println!("Source PolicySet implies Target PolicySet")
        } else {
            println!(
                "Source PolicySet implies Target PolicySet when {}",
                open_req_env
            )
        }
    } else if results.iter().all(|r| !*r) {
        if open_req_env.is_any() {
            println!("Source PolicySet does not imply Target PolicySet")
        } else {
            println!(
                "Source PolicySet does not imply Target PolicySet for all requests where {}",
                open_req_env
            )
        }
    } else if open_req_env.is_any() {
        println!("Source PolicySet implies Target PolicySet for some request signatures")
    } else {
        println!(
            "Source PolicySet implies Target PolicySet for some request signatures where {}",
            open_req_env
        )
    }

    println!();
    println!("Per request signature results:");

    let sig_widths = SigWidths::from_req_envs(req_envs);
    let res_width = 14; // Does Not Imply

    sig_widths.print_header(res_width, "Result");
    for (req_env, result) in zip(req_envs.iter(), results.iter()) {
        let result = if *result { "Implies" } else { "Does Not Imply" };
        sig_widths.print_row(req_env, res_width, result);
    }
    sig_widths.print_footer(res_width);
}

fn print_check_disjoint_results(
    results: &[bool],
    req_envs: &[RequestEnv],
    open_req_env: &OpenRequestEnv,
) {
    if results.iter().all(|r| *r) {
        if open_req_env.is_any() {
            println!("Source PolicySet is disjoint with Target PolicySet")
        } else {
            println!(
                "Source PolicySet is disjoint with Target PolicySet when {}",
                open_req_env
            )
        }
    } else if results.iter().all(|r| !*r) {
        if open_req_env.is_any() {
            println!("Source PolicySet is not disjoint with Target PolicySet")
        } else {
            println!(
                "Source PolicySet is not disjoint with Target PolicySet for all requests where {}",
                open_req_env
            )
        }
    } else if open_req_env.is_any() {
        println!("Source PolicySet is disjoint with Target PolicySet for some request signatures")
    } else {
        println!(
            "Source PolicySet is disjoint with Target PolicySet for some request signatures where {}",
            open_req_env
        )
    }

    println!();
    println!("Per request signature results:");

    let sig_widths = SigWidths::from_req_envs(req_envs);
    let res_width = 12; // Not Disjoint

    sig_widths.print_header(res_width, "Result");
    for (req_env, result) in zip(req_envs.iter(), results.iter()) {
        let result = if *result { "Disjoint" } else { "Not Disjoint" };
        sig_widths.print_row(req_env, res_width, result);
    }
    sig_widths.print_footer(res_width);
}
