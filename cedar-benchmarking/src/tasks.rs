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

use miette::IntoDiagnostic;
use serde::Deserialize;
use std::path::PathBuf;

/// Benchmark targets that can be measured
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum Target {
    PolicyParse,
    JsonPolicyParse,
    ProtobufPolicyParse,
    SchemaParse,
    JsonSchemaParse,
    ProtobufSchemaParse,
    Validation,
    Authorization,
    EntityParseWithSchema,
    EntityParseWithoutSchema,
    ProtobufEntityParse,
}

impl std::fmt::Display for Target {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::PolicyParse => write!(f, "policy_parse"),
            Self::JsonPolicyParse => write!(f, "json_policy_parse"),
            Self::ProtobufPolicyParse => write!(f, "protobuf_policy_parse"),
            Self::SchemaParse => write!(f, "schema_parse"),
            Self::JsonSchemaParse => write!(f, "json_schema_parse"),
            Self::ProtobufSchemaParse => write!(f, "protobuf_schema_parse"),
            Self::Validation => write!(f, "validation"),
            Self::Authorization => write!(f, "authorization"),
            Self::EntityParseWithSchema => write!(f, "entity_parse_with_schema"),
            Self::EntityParseWithoutSchema => write!(f, "entity_parse_without_schema"),
            Self::ProtobufEntityParse => write!(f, "protobuf_entity_parse"),
        }
    }
}

impl std::str::FromStr for Target {
    type Err = String;
    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "policy_parse" => Ok(Self::PolicyParse),
            "json_policy_parse" => Ok(Self::JsonPolicyParse),
            "protobuf_policy_parse" => Ok(Self::ProtobufPolicyParse),
            "schema_parse" => Ok(Self::SchemaParse),
            "json_schema_parse" => Ok(Self::JsonSchemaParse),
            "protobuf_schema_parse" => Ok(Self::ProtobufSchemaParse),
            "validation" => Ok(Self::Validation),
            "authorization" => Ok(Self::Authorization),
            "entity_parse_with_schema" => Ok(Self::EntityParseWithSchema),
            "entity_parse_without_schema" => Ok(Self::EntityParseWithoutSchema),
            "protobuf_entity_parse" => Ok(Self::ProtobufEntityParse),
            _ => Err(format!("unknown target: {s}")),
        }
    }
}

/// A task definition as read from the corpus JSON
#[derive(Debug, Clone, Deserialize)]
pub struct Task {
    pub name: String,
    pub policy_file: Option<PathBuf>,
    pub cedar_schema_file: Option<PathBuf>,
    pub json_schema_file: Option<PathBuf>,
    pub entities_file: Option<PathBuf>,
    #[serde(default)]
    pub exclude_targets: Vec<Target>,
    #[serde(skip)]
    pub only_targets: Option<Vec<Target>>,
}

/// A resolved benchmark task ready for execution
#[derive(Debug, Clone)]
pub enum BenchmarkTask {
    PolicyParse {
        name: String,
        policy_file: PathBuf,
    },
    JsonPolicyParse {
        name: String,
        policy_file: PathBuf,
    },
    ProtobufPolicyParse {
        name: String,
        policy_file: PathBuf,
    },
    SchemaParse {
        name: String,
        cedar_schema_file: PathBuf,
    },
    JsonSchemaParse {
        name: String,
        json_schema_file: PathBuf,
    },
    ProtobufSchemaParse {
        name: String,
        cedar_schema_file: PathBuf,
    },
    Validation {
        name: String,
        policy_file: PathBuf,
        cedar_schema_file: PathBuf,
    },
    Authorization {
        name: String,
        policy_file: PathBuf,
        cedar_schema_file: Option<PathBuf>,
        json_schema_file: PathBuf,
        entities_file: PathBuf,
    },
    EntityParseWithSchema {
        name: String,
        cedar_schema_file: PathBuf,
        entities_file: PathBuf,
    },
    EntityParseWithoutSchema {
        name: String,
        entities_file: PathBuf,
    },
    ProtobufEntityParse {
        name: String,
        entities_file: PathBuf,
    },
}

impl BenchmarkTask {
    pub fn name(&self) -> &str {
        match self {
            Self::PolicyParse { name, .. }
            | Self::JsonPolicyParse { name, .. }
            | Self::ProtobufPolicyParse { name, .. }
            | Self::SchemaParse { name, .. }
            | Self::JsonSchemaParse { name, .. }
            | Self::ProtobufSchemaParse { name, .. }
            | Self::Validation { name, .. }
            | Self::Authorization { name, .. }
            | Self::EntityParseWithSchema { name, .. }
            | Self::EntityParseWithoutSchema { name, .. }
            | Self::ProtobufEntityParse { name, .. } => name,
        }
    }

    pub fn target(&self) -> Target {
        match self {
            Self::PolicyParse { .. } => Target::PolicyParse,
            Self::JsonPolicyParse { .. } => Target::JsonPolicyParse,
            Self::ProtobufPolicyParse { .. } => Target::ProtobufPolicyParse,
            Self::SchemaParse { .. } => Target::SchemaParse,
            Self::JsonSchemaParse { .. } => Target::JsonSchemaParse,
            Self::ProtobufSchemaParse { .. } => Target::ProtobufSchemaParse,
            Self::Validation { .. } => Target::Validation,
            Self::Authorization { .. } => Target::Authorization,
            Self::EntityParseWithSchema { .. } => Target::EntityParseWithSchema,
            Self::EntityParseWithoutSchema { .. } => Target::EntityParseWithoutSchema,
            Self::ProtobufEntityParse { .. } => Target::ProtobufEntityParse,
        }
    }
}

impl Task {
    fn is_target_enabled(&self, target: Target) -> bool {
        self.only_targets
            .as_ref()
            .is_none_or(|only| only.contains(&target))
            && !self.exclude_targets.contains(&target)
    }

    /// Convert into individual benchmark tasks based on available files
    pub fn into_benchmark_tasks(self) -> miette::Result<Vec<BenchmarkTask>> {
        let mut tasks = Vec::new();

        if let Some(ref policy_file) = self.policy_file {
            if self.is_target_enabled(Target::PolicyParse) {
                tasks.push(BenchmarkTask::PolicyParse {
                    name: self.name.clone(),
                    policy_file: policy_file.clone(),
                });
            }
            if self.is_target_enabled(Target::JsonPolicyParse) {
                tasks.push(BenchmarkTask::JsonPolicyParse {
                    name: self.name.clone(),
                    policy_file: policy_file.clone(),
                });
            }
            if self.is_target_enabled(Target::ProtobufPolicyParse) {
                tasks.push(BenchmarkTask::ProtobufPolicyParse {
                    name: self.name.clone(),
                    policy_file: policy_file.clone(),
                });
            }
        }

        if let Some(ref cedar_schema_file) = self.cedar_schema_file {
            if self.is_target_enabled(Target::SchemaParse) {
                tasks.push(BenchmarkTask::SchemaParse {
                    name: self.name.clone(),
                    cedar_schema_file: cedar_schema_file.clone(),
                });
            }
            if self.is_target_enabled(Target::ProtobufSchemaParse) {
                tasks.push(BenchmarkTask::ProtobufSchemaParse {
                    name: self.name.clone(),
                    cedar_schema_file: cedar_schema_file.clone(),
                });
            }
        }

        if let Some(ref json_schema_file) = self.json_schema_file {
            if self.is_target_enabled(Target::JsonSchemaParse) {
                tasks.push(BenchmarkTask::JsonSchemaParse {
                    name: self.name.clone(),
                    json_schema_file: json_schema_file.clone(),
                });
            }
        }

        if let (Some(ref policy_file), Some(ref cedar_schema_file)) =
            (&self.policy_file, &self.cedar_schema_file)
        {
            if self.is_target_enabled(Target::Validation) {
                tasks.push(BenchmarkTask::Validation {
                    name: self.name.clone(),
                    policy_file: policy_file.clone(),
                    cedar_schema_file: cedar_schema_file.clone(),
                });
            }
        }

        if let (Some(ref policy_file), Some(ref json_schema_file), Some(ref entities_file)) = (
            &self.policy_file,
            &self.json_schema_file,
            &self.entities_file,
        ) {
            if self.is_target_enabled(Target::Authorization) {
                tasks.push(BenchmarkTask::Authorization {
                    name: self.name.clone(),
                    policy_file: policy_file.clone(),
                    cedar_schema_file: self.cedar_schema_file.clone(),
                    json_schema_file: json_schema_file.clone(),
                    entities_file: entities_file.clone(),
                });
            }
        }

        if let (Some(ref cedar_schema_file), Some(ref entities_file)) =
            (&self.cedar_schema_file, &self.entities_file)
        {
            if self.is_target_enabled(Target::EntityParseWithSchema) {
                tasks.push(BenchmarkTask::EntityParseWithSchema {
                    name: self.name.clone(),
                    cedar_schema_file: cedar_schema_file.clone(),
                    entities_file: entities_file.clone(),
                });
            }
        }

        if let Some(ref entities_file) = self.entities_file {
            if self.is_target_enabled(Target::EntityParseWithoutSchema) {
                tasks.push(BenchmarkTask::EntityParseWithoutSchema {
                    name: self.name.clone(),
                    entities_file: entities_file.clone(),
                });
            }
            if self.is_target_enabled(Target::ProtobufEntityParse) {
                tasks.push(BenchmarkTask::ProtobufEntityParse {
                    name: self.name.clone(),
                    entities_file: entities_file.clone(),
                });
            }
        }

        if tasks.is_empty() && self.only_targets.is_none() {
            Err(miette::miette!(
                "No benchmark tasks could be created for '{}' — check that the required files exist",
                self.name
            ))
        } else {
            Ok(tasks)
        }
    }
}

/// Load a benchmark corpus from a tasks.json file
pub fn load_corpus(path: &PathBuf, targets: Option<Vec<Target>>) -> miette::Result<Vec<Task>> {
    let f = std::fs::File::open(path).into_diagnostic()?;
    let prefix = path.parent().unwrap_or(std::path::Path::new("."));
    let tasks: Vec<Task> = serde_json::from_reader(f).into_diagnostic()?;
    Ok(tasks
        .into_iter()
        .map(|t| Task {
            name: t.name,
            policy_file: t.policy_file.map(|p| prefix.join(p)),
            cedar_schema_file: t.cedar_schema_file.map(|p| prefix.join(p)),
            json_schema_file: t.json_schema_file.map(|p| prefix.join(p)),
            entities_file: t.entities_file.map(|p| prefix.join(p)),
            exclude_targets: t.exclude_targets,
            only_targets: targets.clone(),
        })
        .collect())
}
