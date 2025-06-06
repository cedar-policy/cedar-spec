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
use crate::analysis;
use crate::cli_enums::{
    AnalysisCommands, CliArgs, Command, EvaluationCommands, ModeEnum, RequestArgsEnum,
    SymCCCommands, ValidationCommands,
};
use crate::err::ExecError;
use crate::evaluation;
use crate::symcc;
use crate::util;
use crate::util::OpenRequestEnv;
use crate::validation;

impl EvaluationCommands {
    /// Execute the task described by the evaluation command
    fn exec(self) -> Result<(), ExecError> {
        match self {
            Self::Authorize {
                policyset_file,
                entities_file,
                req_args,
            } => {
                let policyset = util::parse_policyset(&policyset_file)?;
                let request = RequestArgsEnum::from(req_args).parse()?;
                let entities = util::parse_entities(&entities_file)?;
                evaluation::check_is_authorized(&policyset, &entities, &request)
            }
            Self::Evaluate {
                input_expr_file,
                entities_file,
                req_args,
                expected_expr_file,
            } => {
                let input_expr = util::parse_expression(&input_expr_file)?;
                let entities = util::parse_entities(&entities_file)?;
                let request = RequestArgsEnum::from(req_args).parse()?;
                let output_expr = expected_expr_file
                    .map(|fname| util::parse_expression(&fname))
                    .transpose()?;
                evaluation::evaluate(&input_expr, &entities, &request, output_expr.as_ref())
            }
        }
    }
}

impl ValidationCommands {
    /// Execute the task described by the validation request
    fn exec(self) -> Result<(), ExecError> {
        match self {
            Self::PolicySet {
                policyset_file,
                schema_file,
                validation_mode,
            } => {
                let policyset = util::parse_policyset(&policyset_file)?;
                let schema = util::parse_schema(&schema_file)?;
                let validation_mode = validation_mode.to_cedar();
                validation::validate(&policyset, &schema, &validation_mode)
            }
            Self::Level {
                policyset_file,
                schema_file,
                level,
            } => {
                let policyset = util::parse_policyset(&policyset_file)?;
                let schema = util::parse_schema(&schema_file)?;
                validation::level_validate(&policyset, &schema, level)
            }
            Self::Request {
                schema_file,
                req_args,
            } => {
                let schema = util::parse_schema(&schema_file)?;
                let request = RequestArgsEnum::from(req_args).parse()?;
                validation::validate_request(&schema, &request)
            }
            Self::Entities {
                schema_file,
                entities_file,
            } => {
                let schema = util::parse_schema(&schema_file)?;
                let entities = util::parse_entities(&entities_file)?;
                validation::validate_entities(&schema, &entities)
            }
        }
    }
}

impl AnalysisCommands {
    /// Execute the task described by the analysis command
    fn exec(self) -> Result<(), ExecError> {
        match self {
            Self::Policies { args } => {
                let policyset = util::parse_policyset(&args.policyset_file)?;
                let schema = util::parse_schema(&args.schema_file)?;
                let json_output = args.json_output;
                analysis::analyze_policyset(policyset, schema, json_output)
            }
            Self::Compare { args } => {
                let src_policyset = util::parse_policyset(&args.source_policyset_file)?;
                let tgt_policyset = util::parse_policyset(&args.target_policyset_file)?;
                let schema = util::parse_schema(&args.schema_file)?;
                let json_output = args.json_output;
                analysis::compare_policysets(src_policyset, tgt_policyset, schema, json_output)
            }
        }
    }
}

impl SymCCCommands {
    /// Execute the task described by the sym-eval command
    fn exec(self) -> Result<(), ExecError> {
        match self {
            Self::CheckNeverErrors {
                args,
                mode,
                req_env,
            } => {
                let policy = util::parse_policy(&args.policy_file)?;
                let schema = util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        symcc::run_check_never_errors(policy, schema, &req_env)
                    }
                    ModeEnum::PrintSMTLib => {
                        symcc::print_check_never_errors(policy, schema, &req_env)
                    }
                }
            }
            Self::CheckAlwaysAllows {
                args,
                mode,
                req_env,
            } => {
                let policyset = util::parse_policyset(&args.policyset_file)?;
                let schema = util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        symcc::run_check_always_allows(policyset, schema, &req_env)
                    }
                    ModeEnum::PrintSMTLib => {
                        symcc::print_check_always_allows(policyset, schema, &req_env)
                    }
                }
            }
            Self::CheckAlwaysDenies {
                args,
                mode,
                req_env,
            } => {
                let policyset = util::parse_policyset(&args.policyset_file)?;
                let schema = util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        symcc::run_check_always_denies(policyset, schema, &req_env)
                    }
                    ModeEnum::PrintSMTLib => {
                        symcc::print_check_always_denies(policyset, schema, &req_env)
                    }
                }
            }
            Self::CheckEquivalent {
                args,
                mode,
                req_env,
            } => {
                let src_policyset = util::parse_policyset(&args.source_policyset_file)?;
                let tgt_policyset = util::parse_policyset(&args.target_policyset_file)?;
                let schema = util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        symcc::run_check_equivalent(src_policyset, tgt_policyset, schema, &req_env)
                    }
                    ModeEnum::PrintSMTLib => symcc::print_check_equivalent(
                        src_policyset,
                        tgt_policyset,
                        schema,
                        &req_env,
                    ),
                }
            }
            Self::CheckImplies {
                args,
                mode,
                req_env,
            } => {
                let src_policyset = util::parse_policyset(&args.source_policyset_file)?;
                let tgt_policyset = util::parse_policyset(&args.target_policyset_file)?;
                let schema = util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        symcc::run_check_implies(src_policyset, tgt_policyset, schema, &req_env)
                    }
                    ModeEnum::PrintSMTLib => {
                        symcc::print_check_implies(src_policyset, tgt_policyset, schema, &req_env)
                    }
                }
            }
            Self::CheckDisjoint {
                args,
                mode,
                req_env,
            } => {
                let src_policyset = util::parse_policyset(&args.source_policyset_file)?;
                let tgt_policyset = util::parse_policyset(&args.target_policyset_file)?;
                let schema = util::parse_schema(&args.schema_file)?;
                let req_env = OpenRequestEnv::from_request_args(req_env)?;
                match ModeEnum::from(mode) {
                    ModeEnum::RunAnalysis => {
                        symcc::run_check_disjoint(src_policyset, tgt_policyset, schema, &req_env)
                    }
                    ModeEnum::PrintSMTLib => {
                        symcc::print_check_disjoint(src_policyset, tgt_policyset, schema, &req_env)
                    }
                }
            }
        }
    }
}

impl CliArgs {
    /// Execute the task described by the command-line arguments
    pub fn exec(self) -> Result<(), ExecError> {
        match self.command {
            Command::Analyze { command } => command.exec(),
            Command::Evaluate { command } => command.exec(),
            Command::Validate { command } => command.exec(),
            Command::Symcc { command } => command.exec(),
        }
    }
}
