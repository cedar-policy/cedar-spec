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

use std::{fs::File, io};

use anyhow::{anyhow, Result};
use arbitrary::Unstructured;
use cedar_policy_core::entities::{Entities, TCComputation};
use cedar_policy_core::extensions::Extensions;
use cedar_policy_generators::{
    hierarchy::{EntityUIDGenMode, HierarchyGenerator, HierarchyGeneratorMode, NumEntities},
    schema::Schema,
    settings::ABACSettings,
};
use cedar_policy_validator::{json_schema, CoreSchema, RawName, ValidatorSchema};
use clap::{Args, Parser, Subcommand};
use rand::{thread_rng, Rng};

#[derive(Parser, Debug)]
struct Cli {
    /// Random byte length
    #[arg(short, long, default_value_t = 4096)]
    byte_length: u16,

    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
pub enum Commands {
    /// Generate random hierarchy
    Hierarchy(HierarchyArgs),
}

#[derive(Args, Debug)]
pub struct HierarchyArgs {
    /// Schema file
    #[arg(short, long = "schema", value_name = "FILE")]
    pub schema_file: String,
    /// Exact number of entities to generate
    /// (if this is omitted, then you will get 1 to max_depth per entity type)
    #[arg(long)]
    pub num_entities: Option<usize>,
    /// Maximum depth
    #[arg(long, default_value_t = 4)]
    pub max_depth: usize,
    /// Maximum width
    #[arg(long, default_value_t = 4)]
    pub max_width: usize,
    #[arg(long, default_value_t = EntityUIDGenMode::default_nanoid_len())]
    pub uid_length: usize,
}

impl From<&HierarchyArgs> for ABACSettings {
    fn from(value: &HierarchyArgs) -> Self {
        Self {
            match_types: true,
            enable_extensions: true,
            max_depth: value.max_depth,
            max_width: value.max_width,
            enable_additional_attributes: false,
            enable_like: true,
            enable_action_groups_and_attrs: true,
            enable_arbitrary_func_call: false,
            enable_unknowns: false,
            enable_unspecified_apply_spec: true,
            enable_action_in_constraints: true,
        }
    }
}

fn generate_hierarchy_from_schema(byte_length: usize, args: &HierarchyArgs) -> Result<Entities> {
    let f = File::open(&args.schema_file)?;
    let fragment = json_schema::Fragment::<RawName>::from_file(f)?;
    let mut rng = thread_rng();
    let mut bytes = Vec::with_capacity(byte_length);
    bytes.resize_with(byte_length, || rng.gen());
    let mut u = Unstructured::new(&bytes);
    let schema = Schema::from_raw_schemafrag(fragment, args.into(), &mut u)
        .map_err(|err| anyhow!("failed to construct `Schema`: {err:#?}"))?;
    let h = HierarchyGenerator {
        mode: HierarchyGeneratorMode::SchemaBased { schema: &schema },
        uid_gen_mode: EntityUIDGenMode::Nanoid(args.uid_length),
        num_entities: match args.num_entities {
            Some(exact_num) => NumEntities::Exactly(exact_num),
            None => NumEntities::RangePerEntityType(1..=args.max_depth),
        },
        u: &mut u,
        extensions: Extensions::all_available(),
    }
    .generate()
    .map_err(|err| anyhow!("failed to generate hierarchy: {err:#?}"))?;
    let vschema = ValidatorSchema::try_from(schema)
        .map_err(|err| anyhow!("failed to convert schema to ValidatorSchema: {err}"))?;
    let coreschema = CoreSchema::new(&vschema);
    // this is just to ensure no cycles.
    // we throw away the `Entities` built with `ComputeNow`, because we want to
    // generate hierarchies that aren't necessarily TC-closed.
    Entities::from_entities(
        h.entities().cloned(),
        Some(&coreschema),
        TCComputation::ComputeNow,
        Extensions::all_available(),
    )?;
    Ok(Entities::from_entities(
        h.entities().cloned(),
        Some(&coreschema),
        // use `AssumeAlreadyComputed` because we want a hierarchy that isn't
        // necessarily TC-closed.
        TCComputation::AssumeAlreadyComputed,
        Extensions::all_available(),
    )?)
}

fn main() {
    let cli = Cli::parse();
    match &cli.command {
        Commands::Hierarchy(args) => {
            match generate_hierarchy_from_schema(cli.byte_length as usize, args) {
                Ok(h) => {
                    h.write_to_json(io::stdout())
                        .unwrap_or_else(|err| eprintln!("cannot convert entities to JSON: {err}"));
                }
                Err(err) => {
                    eprintln!("{err}");
                }
            }
        }
    }
}
