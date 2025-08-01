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
use crate::web_analysis;
use crate::web_cli_enums::{
    AnalysisCommands, CliArgs, Command, ModeEnum,
    SymCCCommands,
};
use crate::web_err::ExecError;
use crate::web_symcc;
use crate::web_util;
use crate::web_util::OpenRequestEnv;

impl AnalysisCommands {
    /// Execute the task described by the analysis command
    async fn exec(self) -> Result<String, ExecError> {
        match self {
            Self::Policies { args } => {
                let policyset = web_util::parse_policyset(&args.policyset_file)?;
                let schema = web_util::parse_schema(&args.schema_file)?;
                web_analysis::analyze_policyset(policyset, schema).await
            }
            Self::Compare { args } => {
                let src_policyset = web_util::parse_policyset(&args.source_policyset_file)?;
                let tgt_policyset = web_util::parse_policyset(&args.target_policyset_file)?;
                let schema = web_util::parse_schema(&args.schema_file)?;
                web_analysis::compare_policysets(src_policyset, tgt_policyset, schema).await
            }
        }
    }
}

impl SymCCCommands {
    /// Execute the task described by the sym-eval command
    async fn exec(self) -> Result<(), ExecError> {
        match self {
            Self::CheckNeverErrors {
                args,
                mode,
                req_env,
            } => {
                let policy = web_util::parse_policy(&args.policy_file)?;
                let schema = web_util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        web_symcc::run_check_never_errors(policy, schema, &req_env).await
                    }
                }
            }
            Self::CheckAlwaysAllows {
                args,
                mode,
                req_env,
            } => {
                let policyset = web_util::parse_policyset(&args.policyset_file)?;
                let schema = web_util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        web_symcc::run_check_always_allows(policyset, schema, &req_env).await
                    }
                }
            }
            Self::CheckAlwaysDenies {
                args,
                mode,
                req_env,
            } => {
                let policyset = web_util::parse_policyset(&args.policyset_file)?;
                let schema = web_util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        web_symcc::run_check_always_denies(policyset, schema, &req_env).await
                    }
                }
            }
            Self::CheckEquivalent {
                args,
                mode,
                req_env,
            } => {
                let src_policyset = web_util::parse_policyset(&args.source_policyset_file)?;
                let tgt_policyset = web_util::parse_policyset(&args.target_policyset_file)?;
                let schema = web_util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        web_symcc::run_check_equivalent(src_policyset, tgt_policyset, schema, &req_env).await
                    }
                }
            }
            Self::CheckImplies {
                args,
                mode,
                req_env,
            } => {
                let src_policyset = web_util::parse_policyset(&args.source_policyset_file)?;
                let tgt_policyset = web_util::parse_policyset(&args.target_policyset_file)?;
                let schema = web_util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        web_symcc::run_check_implies(src_policyset, tgt_policyset, schema, &req_env).await
                    }
                }
            }
            Self::CheckDisjoint {
                args,
                mode,
                req_env,
            } => {
                let src_policyset = web_util::parse_policyset(&args.source_policyset_file)?;
                let tgt_policyset = web_util::parse_policyset(&args.target_policyset_file)?;
                let schema = web_util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        web_symcc::run_check_disjoint(src_policyset, tgt_policyset, schema, &req_env).await
                    }
                }
            }
        }
    }
}

impl CliArgs {
    /// Execute the task described by the command-line arguments
    pub async fn exec(self) -> Result<String, ExecError> {
        match self.command {
            Command::Analyze { command } => command.exec().await,
            Command::Symcc { command } => {
                command.exec().await?;
                Ok("SymCC command executed successfully".to_string())
            },
        }
    }
}
