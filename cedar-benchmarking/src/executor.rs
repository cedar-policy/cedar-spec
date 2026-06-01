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

use crate::output::TimingInfo;
use crate::request::generate_requests;
use crate::tasks::{BenchmarkTask, Target};
use cedar_policy::proto::traits::Protobuf;
use cedar_policy::{Authorizer, PolicySet, Request, Schema};
use cedar_policy_core::entities::{EntityJsonParser, NoEntitiesSchema, TCComputation};
use cedar_policy_core::extensions::Extensions;
use core::hint::black_box;
use core::time::Duration;
use miette::{Context, IntoDiagnostic};
use std::path::Path;
use std::time::Instant;

/// Executes benchmarks with a configurable number of trials
#[derive(Debug, Copy, Clone)]
pub struct BenchmarkExecutor {
    trials: usize,
}

impl BenchmarkExecutor {
    pub const fn new(trials: usize) -> Self {
        Self { trials }
    }

    pub fn run(self, task: &BenchmarkTask) -> miette::Result<(Target, String, TimingInfo)> {
        let timing = match task {
            BenchmarkTask::PolicyParse { policy_file, .. } => {
                self.bench_policy_parsing(policy_file)
            }
            BenchmarkTask::JsonPolicyParse { policy_file, .. } => {
                self.bench_json_policy_parsing(policy_file)
            }
            BenchmarkTask::ProtobufPolicyParse { policy_file, .. } => {
                self.bench_protobuf_policy_parsing(policy_file)
            }
            BenchmarkTask::SchemaParse {
                cedar_schema_file, ..
            } => self.bench_schema_parsing(cedar_schema_file),
            BenchmarkTask::JsonSchemaParse {
                json_schema_file, ..
            } => self.bench_json_schema_parsing(json_schema_file),
            BenchmarkTask::ProtobufSchemaParse {
                cedar_schema_file, ..
            } => self.bench_protobuf_schema_parsing(cedar_schema_file),
            BenchmarkTask::Validation {
                policy_file,
                cedar_schema_file,
                ..
            } => self.bench_validation(policy_file, cedar_schema_file),
            BenchmarkTask::Authorization {
                policy_file,
                cedar_schema_file,
                json_schema_file,
                entities_file,
                ..
            } => self.bench_authorization(
                policy_file,
                cedar_schema_file.as_deref(),
                json_schema_file,
                entities_file,
            ),
            BenchmarkTask::EntityParseWithSchema {
                cedar_schema_file,
                entities_file,
                ..
            } => self.bench_entity_parsing_with_schema(cedar_schema_file, entities_file),
            BenchmarkTask::EntityParseWithoutSchema { entities_file, .. } => {
                self.bench_entity_parsing_without_schema(entities_file)
            }
            BenchmarkTask::ProtobufEntityParse { entities_file, .. } => {
                self.bench_protobuf_entity_parsing(entities_file)
            }
        }
        .wrap_err_with(|| {
            format!(
                "Error executing `{}` target for `{}` benchmark",
                task.target(),
                task.name()
            )
        })?;

        Ok((task.target(), task.name().to_string(), timing))
    }

    fn bench_policy_parsing(self, policy_file: &Path) -> miette::Result<TimingInfo> {
        let src = std::fs::read_to_string(policy_file).into_diagnostic()?;
        Ok(self.benchmark(
            |src| {
                src.parse::<PolicySet>().expect("policy parse failed");
            },
            src,
        ))
    }

    fn bench_json_policy_parsing(self, policy_file: &Path) -> miette::Result<TimingInfo> {
        let src = std::fs::read_to_string(policy_file).into_diagnostic()?;
        let policy_set = src.parse::<PolicySet>()?;
        let json_policy =
            serde_json::to_string(&policy_set.to_json().into_diagnostic()?).into_diagnostic()?;
        Ok(self.benchmark(
            |json| {
                PolicySet::from_json_str(json).expect("json policy parse failed");
            },
            &json_policy,
        ))
    }

    fn bench_protobuf_policy_parsing(self, policy_file: &Path) -> miette::Result<TimingInfo> {
        let src = std::fs::read_to_string(policy_file).into_diagnostic()?;
        let policy_set = src.parse::<PolicySet>()?;
        let proto = policy_set.encode();
        Ok(self.benchmark(
            |proto| {
                PolicySet::decode(proto.as_slice()).expect("protobuf policy parse failed");
            },
            &proto,
        ))
    }

    fn bench_schema_parsing(self, schema_file: &Path) -> miette::Result<TimingInfo> {
        let src = std::fs::read_to_string(schema_file).into_diagnostic()?;
        Ok(self.benchmark(
            |src| {
                let (_, _) = Schema::from_cedarschema_str(src).expect("schema parse failed");
            },
            &src,
        ))
    }

    fn bench_json_schema_parsing(self, json_schema_file: &Path) -> miette::Result<TimingInfo> {
        let src = std::fs::read_to_string(json_schema_file).into_diagnostic()?;
        Ok(self.benchmark(
            |src| {
                Schema::from_json_str(src).expect("json schema parse failed");
            },
            &src,
        ))
    }

    fn bench_protobuf_schema_parsing(self, schema_file: &Path) -> miette::Result<TimingInfo> {
        let schema = Self::load_cedar_schema(schema_file)?;
        let proto = schema.encode();
        Ok(self.benchmark(
            |proto| {
                Schema::decode(proto.as_slice()).expect("protobuf schema parse failed");
            },
            &proto,
        ))
    }

    fn bench_validation(
        self,
        policy_file: &Path,
        schema_file: &Path,
    ) -> miette::Result<TimingInfo> {
        let src = std::fs::read_to_string(policy_file).into_diagnostic()?;
        let policies = src.parse::<PolicySet>()?;
        let schema = Self::load_cedar_schema(schema_file)?;
        let validator = cedar_policy::Validator::new(schema);
        Ok(self.benchmark(
            |policies| {
                validator.validate(policies, cedar_policy::ValidationMode::Strict);
            },
            &policies,
        ))
    }

    fn bench_authorization(
        self,
        policy_file: &Path,
        cedar_schema_file: Option<&Path>,
        json_schema_file: &Path,
        entities_file: &Path,
    ) -> miette::Result<TimingInfo> {
        let src = std::fs::read_to_string(policy_file).into_diagnostic()?;
        let policies = src.parse::<PolicySet>()?;
        let schema = cedar_schema_file.map(Self::load_cedar_schema).transpose()?;
        let requests = Self::generate_auth_requests(json_schema_file, entities_file)?;
        let entities_str = std::fs::read_to_string(entities_file).into_diagnostic()?;
        let entities = cedar_policy::Entities::from_json_str(&entities_str, schema.as_ref())
            .into_diagnostic()?;
        let authorizer = Authorizer::new();
        Ok(self.benchmark(
            |requests| {
                for request in requests {
                    authorizer.is_authorized(request, &policies, &entities);
                }
            },
            &requests,
        ))
    }

    fn bench_entity_parsing_with_schema(
        self,
        cedar_schema_file: &Path,
        entities_file: &Path,
    ) -> miette::Result<TimingInfo> {
        let entities_str = std::fs::read_to_string(entities_file).into_diagnostic()?;
        let schema = Self::load_cedar_schema(cedar_schema_file)?;
        Ok(self.benchmark(
            |(entities_str, schema)| {
                cedar_policy::Entities::from_json_str(entities_str, Some(schema))
                    .expect("entity parse failed");
            },
            (&entities_str, &schema),
        ))
    }

    fn bench_entity_parsing_without_schema(
        self,
        entities_file: &Path,
    ) -> miette::Result<TimingInfo> {
        let entities_str = std::fs::read_to_string(entities_file).into_diagnostic()?;
        Ok(self.benchmark(
            |entities_str| {
                cedar_policy::Entities::from_json_str(entities_str, None)
                    .expect("entity parse failed");
            },
            &entities_str,
        ))
    }

    fn bench_protobuf_entity_parsing(self, entities_file: &Path) -> miette::Result<TimingInfo> {
        let entities_str = std::fs::read_to_string(entities_file).into_diagnostic()?;
        let entities =
            cedar_policy::Entities::from_json_str(&entities_str, None).into_diagnostic()?;
        let proto = entities.encode();
        Ok(self.benchmark(
            |proto| {
                cedar_policy::Entities::decode(proto.as_slice())
                    .expect("protobuf entity parse failed");
            },
            &proto,
        ))
    }

    fn load_cedar_schema(schema_file: &Path) -> miette::Result<Schema> {
        let src = std::fs::read_to_string(schema_file).into_diagnostic()?;
        let schema = if schema_file.extension().and_then(|s| s.to_str()) == Some("json") {
            Schema::from_json_str(&src)?
        } else {
            Schema::from_cedarschema_str(&src)?.0
        };
        Ok(schema)
    }

    fn generate_auth_requests(
        json_schema_file: &Path,
        entities_file: &Path,
    ) -> miette::Result<Vec<Request>> {
        let entities_str = std::fs::read_to_string(entities_file).into_diagnostic()?;
        let parser: EntityJsonParser<'_, '_, NoEntitiesSchema> =
            EntityJsonParser::new(None, Extensions::all_available(), TCComputation::ComputeNow);
        let entities = parser.from_json_str(&entities_str).into_diagnostic()?;
        let frag = cedar_policy_core::validator::json_schema::Fragment::from_json_file(
            std::fs::File::open(json_schema_file).into_diagnostic()?,
        )
        .into_diagnostic()?;
        Ok(generate_requests(&entities, &frag))
    }

    /// Run `f(x)` for `trials` iterations, recording timing statistics
    fn benchmark<T: Clone>(self, f: impl Fn(T), x: T) -> TimingInfo {
        let mut runs = Vec::with_capacity(self.trials);

        // Warm-up run
        f(x.clone());

        for _ in 0..self.trials {
            let dur = Self::time(&f, x.clone());
            runs.push(dur.as_micros());
        }

        TimingInfo::from_runs(runs)
    }

    fn time<T>(f: impl Fn(T), x: T) -> Duration {
        let start = Instant::now();
        black_box(f)(black_box(x));
        start.elapsed()
    }
}
