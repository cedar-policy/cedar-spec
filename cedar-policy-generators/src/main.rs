use std::{fs::File, io};

use anyhow::{anyhow, Result};
use arbitrary::Unstructured;
use cedar_policy_core::entities::{Entities, TCComputation};
use cedar_policy_generators::{schema::Schema, settings::ABACSettings};
use cedar_policy_validator::SchemaFragment;
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
    /// Maximum depth
    #[arg(long, default_value_t = 4)]
    pub max_depth: usize,
    /// Maximum width
    #[arg(long, default_value_t = 4)]
    pub max_width: usize,
}

impl From<&HierarchyArgs> for ABACSettings {
    fn from(value: &HierarchyArgs) -> Self {
        Self {
            match_types: false,
            enable_extensions: true,
            max_depth: value.max_depth,
            max_width: value.max_width,
            enable_additional_attributes: false,
            enable_like: false,
            enable_action_groups_and_attrs: true,
            enable_arbitrary_func_call: false,
            enable_unknowns: false,
        }
    }
}

fn generate_hierarchy_from_schema(byte_length: usize, args: &HierarchyArgs) -> Result<Entities> {
    let f = File::open(args.schema_file.clone())?;
    let fragment = SchemaFragment::from_file(f)?;
    let mut rng = thread_rng();
    let mut bytes = Vec::new();
    bytes.resize_with(byte_length, || rng.gen());
    let mut u = Unstructured::new(&bytes);
    let schema = Schema::from_schemafrag(fragment.clone(), args.into(), &mut u)
        .map_err(|err| anyhow!(format!("failed to construct `Schema`: {:#?}", err)))?;
    let h = schema
        .arbitrary_hierarchy(&mut u)
        .map_err(|err| anyhow!(format!("failed to generate hierarchy: {:#?}", err)))?;
    Entities::from_entities(
        h.entities().into_iter().map(|e| e.clone()),
        TCComputation::ComputeNow,
    )?;
    Ok(Entities::from_entities(
        h.entities().into_iter().map(|e| e.clone()),
        TCComputation::AssumeAlreadyComputed,
    )?)
}

fn main() {
    let cli = Cli::parse();
    match &cli.command {
        Commands::Hierarchy(args) => {
            match generate_hierarchy_from_schema(cli.byte_length as usize, args) {
                Ok(h) => {
                    h.write_to_json(io::stdout()).unwrap_or_else(|err| {
                        eprintln!("{}", format!("cannot convert entities to JSON: {}", err))
                    });
                }
                Err(err) => {
                    eprintln!("{}", err);
                }
            }
        }
    }
}
