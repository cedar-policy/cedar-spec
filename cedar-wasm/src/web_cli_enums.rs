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
use crate::web_err::ExecError;
use crate::web_util;
use clap::{ArgAction, Args, Parser, Subcommand};
use serde::{Serialize, Deserialize};
use std::path::PathBuf;

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub(crate) struct PolicyAnalysisArgs {
    /// A file containing the Policy to be analyzed
    #[clap(required = true)]
    pub(crate) policy_file: PathBuf,
    /// A file containing the schema for which the Policy is to be analyzed against
    #[clap(required = true)]
    pub(crate) schema_file: PathBuf,
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub(crate) struct PolicySetAnalysisArgs {
    /// A file containing the PolicySet to be analyzed
    #[clap(required = true)]
    pub(crate) policyset_file: PathBuf,
    /// A file containing the schema for which the PolicySet is to be analyzed against
    #[clap(required = true)]
    pub(crate) schema_file: PathBuf,
    /// Whether to output the compare policy sets output in .json format
    #[clap(long, short, action=ArgAction::SetTrue)]
    pub(crate) json_output: bool,
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
pub(crate) struct ComparePolicySetAnalysisArgs {
    /// A file containing the first PolicySet to be analyzed
    #[clap(required = true)]
    pub(crate) source_policyset_file: PathBuf,
    /// A file containing the second PolicySet to be analyzed
    #[clap(required = true)]
    pub(crate) target_policyset_file: PathBuf,
    /// A file containing the schema for which the PolicySet(s) are to be analyzed against
    #[clap(required = true)]
    pub(crate) schema_file: PathBuf,
    /// Whether to output the compare policy sets output in .json format
    #[clap(long, short, action=ArgAction::SetTrue)]
    pub(crate) json_output: bool,
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
#[clap(next_help_heading = "Execution Modes")]
pub(crate) struct Mode {
    /// Run the SMT formula produced by the provided backend encoder via CVC5 [default]
    #[arg(long, global=true)]
    run_analysis: bool,
}

pub(crate) enum ModeEnum {
    RunAnalysis,
}

impl From<Mode> for ModeEnum {
    /// Convert from `Mode` struct which works well with clap to `ModeEnum`
    /// which is much nicer to use and pattern-match on.
    fn from(_mode : Mode) -> Self {
        return ModeEnum::RunAnalysis;
    }
}

/// Need to refactor into a struct that has both options and make them conflict with each other...
/// Then provide a translation into an Enum of this form for easier pattern matching.
#[derive(Args, Clone, Debug, Serialize, Deserialize)]
#[clap(next_help_heading = "Request Arguments (required)")]
#[serde(rename_all = "kebab-case")]
pub(crate) struct RequestArgs {
    /// The requested principal
    #[arg(
        long,
        value_name = "PRINCIPAL_NAME",
        conflicts_with = "request_file",
        required_unless_present = "request_file"
    )]
    principal: Option<String>,
    /// The requested action
    #[arg(
        long,
        value_name = "ACTION_ID",
        conflicts_with = "request_file",
        required_unless_present = "request_file"
    )]
    action: Option<String>,
    /// The requested resource
    #[arg(
        long,
        value_name = "RESOURCE_NAME",
        conflicts_with = "request_file",
        required_unless_present = "request_file"
    )]
    resource: Option<String>,
    /// The context as a JSON string [default {}]
    #[arg(long, value_name = "CONTEXT", conflicts_with_all = ["request_file", "context_file"], requires = "principal", requires = "action", requires = "resource")]
    context: Option<String>,
    /// A file containign the context in JSON
    #[arg(long, value_name = "CONTEXT_FILE", conflicts_with_all = ["request_file", "context"], requires = "principal", requires = "action", requires = "resource")]
    context_file: Option<PathBuf>,
    /// A file containing a request (principal, action, resource, context) in JSON format
    #[arg(long, value_name = "REQUEST_FILE", conflicts_with_all = ["principal", "action", "resource", "context", "context_file"])]
    request_file: Option<PathBuf>,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) enum ContextArg {
    FromString { json_str: String },
    FromFile { file_name: PathBuf },
    Default,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
pub(crate) enum RequestArgsEnum {
    FromArgs {
        principal: String,
        action: String,
        resource: String,
        context: ContextArg,
    },
    FromFile {
        file_name: PathBuf,
    },
}

impl From<RequestArgs> for RequestArgsEnum {
    /// Convert from RequestArgs to RequestArgsEnum for a more user-friendly representation/pattern matching
    fn from(req_args: RequestArgs) -> Self {
        match req_args.request_file {
            Some(fname) => Self::FromFile { file_name: fname },
            None => {
                let context = match (req_args.context, req_args.context_file) {
                    (Some(ctx_str), _) => ContextArg::FromString { json_str: ctx_str },
                    (_, Some(ctx_file)) => ContextArg::FromFile {
                        file_name: ctx_file,
                    },
                    (_, _) => ContextArg::Default,
                };
                match (req_args.principal, req_args.action, req_args.resource) {
                    (Some(p), Some(a), Some(r)) => Self::FromArgs {
                        principal: p,
                        action: a,
                        resource: r,
                        context,
                    },
                    (_, _, _) => panic!("Error parsing args. Principal, Action, and Resource are required if request_file is not provided"),
                }
            }
        }
    }
}

#[derive(Args, Clone, Debug, Serialize, Deserialize)]
#[clap(next_help_heading = "Request Environment Options")]
#[serde(rename_all = "kebab-case")]
pub(crate) struct RequestEnvArgs {
    /// Restrict Analysis to Request Environments for the given PrincipalType
    #[arg(long, value_name = "PRINCIPAL_TYPE_NAME", global = true)]
    principal_type: Option<String>,
    /// Restrict Analysis to Request Environmetns for the given Action
    #[arg(long, value_name = "ACTION_NAME", global = true)]
    action_name: Option<String>,
    /// Restrict Analysis to Request Environments for the given ResourceType
    #[arg(long, value_name = "RESOURCE_TYPE_NAME", global = true)]
    resource_type: Option<String>,
}

impl web_util::OpenRequestEnv {
    /// Function to convert from the CLI struct for specifying a request type to an OpenRequest type
    /// which converts each string to the corresponding Cedar Type (i.e., `EntityType`` or `EntityUID`).
    pub(crate) fn from_request_args(
        value: RequestEnvArgs,
    ) -> Result<web_util::OpenRequestEnv, ExecError> {
        web_util::OpenRequestEnv::new(value.principal_type, value.action_name, value.resource_type)
    }
}

#[allow(clippy::enum_variant_names)]
#[derive(Clone, Debug, Serialize, Subcommand, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum SymCCCommands {
    /// Check if the provided Policy never errors
    CheckNeverErrors {
        #[clap(flatten)]
        args: PolicyAnalysisArgs,
        #[clap(flatten)]
        mode: Mode,
        #[clap(flatten)]
        req_env: RequestEnvArgs,
    },
    /// Check if the provided PolicySet allows all authorization requests
    CheckAlwaysAllows {
        #[clap(flatten)]
        args: PolicySetAnalysisArgs,
        #[clap(flatten)]
        mode: Mode,
        #[clap(flatten)]
        req_env: RequestEnvArgs,
    },
    /// Check if the provided PolicySet denies all authorization requests
    CheckAlwaysDenies {
        #[clap(flatten)]
        args: PolicySetAnalysisArgs,
        #[clap(flatten)]
        mode: Mode,
        #[clap(flatten)]
        req_env: RequestEnvArgs,
    },
    /// Check if the source and target PolicySets are equivalent
    CheckEquivalent {
        #[clap(flatten)]
        args: ComparePolicySetAnalysisArgs,
        #[clap(flatten)]
        mode: Mode,
        #[clap(flatten)]
        req_env: RequestEnvArgs,
    },
    /// Check if the target PolicySet authorizes all requests that the source PolicySet authorizes
    CheckImplies {
        #[clap(flatten)]
        args: ComparePolicySetAnalysisArgs,
        #[clap(flatten)]
        mode: Mode,
        #[clap(flatten)]
        req_env: RequestEnvArgs,
    },
    /// Check if the source and target PolicySets are disjoint (there is no authorization request that both PolicySets allow)
    CheckDisjoint {
        #[clap(flatten)]
        args: ComparePolicySetAnalysisArgs,
        #[clap(flatten)]
        mode: Mode,
        #[clap(flatten)]
        req_env: RequestEnvArgs,
    },
}

#[derive(Clone, Debug, Serialize, Subcommand, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum AnalysisCommands {
    /// Analyze a PolicySet
    Policies {
        #[clap(flatten)]
        args: PolicySetAnalysisArgs,
    },
    /// Compare the source PolicySet against the target PolicySet
    Compare {
        #[clap(flatten)]
        args: ComparePolicySetAnalysisArgs,
    },
}

#[derive(Clone, Debug, Serialize, Subcommand, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(crate) enum Command {
    /// Run the Cedar Analyzer
    Analyze {
        #[clap(subcommand)]
        command: AnalysisCommands,
    },
    /// Run the Cedar Symbolic Compiler
    Symcc {
        #[clap(subcommand)]
        command: SymCCCommands,
    },
}

/// Command Line Interface for Cedar Lean
#[derive(Parser, Debug, Deserialize)]
#[clap(name = "cedar-cli", version)]
pub struct CliArgs {
    #[clap(subcommand)]
    pub(crate) command: Command,
}
