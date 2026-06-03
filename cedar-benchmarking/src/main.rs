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

mod executor;
mod output;
pub mod request;
mod tasks;

use clap::{Parser, ValueEnum};
use miette::IntoDiagnostic;
use output::{BenchmarkOutput, BenchmarkResult, SystemInfo};
use std::path::PathBuf;
use tasks::Target;

#[derive(Debug, Clone, ValueEnum)]
enum OutputFormat {
    Json,
    Table,
}

#[derive(Parser, Debug)]
#[command(
    name = "cedar-benchmarking",
    about = "Benchmark tool for the Cedar policy language",
    version
)]
struct Args {
    /// Path to the benchmark corpus (tasks.json)
    #[arg(short, long)]
    corpus: PathBuf,

    /// Only run specific targets (comma-separated)
    #[arg(short, long, value_delimiter = ',')]
    targets: Option<Vec<Target>>,

    /// Number of trials per benchmark
    #[arg(long, default_value = "1000")]
    trials: usize,

    /// Output format
    #[arg(short, long, value_enum, default_value = "json")]
    output: OutputFormat,
}

fn main() -> miette::Result<()> {
    let args = Args::parse();
    let tasks = tasks::load_corpus(&args.corpus, args.targets.as_deref())?;

    let exec = executor::BenchmarkExecutor::new(args.trials);
    let mut results = Vec::new();

    for task in tasks {
        for bench_task in task.into_benchmark_tasks()? {
            let (target, name, timing) = exec.run(&bench_task)?;
            results.push(BenchmarkResult {
                benchmark: name,
                target: target.to_string(),
                trials: args.trials,
                unit: "microseconds".to_string(),
                average: timing.average,
                min: timing.min,
                max: timing.max,
                stddev: timing.stddev,
                iqr: timing.iqr,
                p50: timing.p50,
                p95: timing.p95,
                p99: timing.p99,
            });
        }
    }

    let output = BenchmarkOutput {
        cedar_version: cedar_policy::get_sdk_version().to_string(),
        system: SystemInfo::collect(),
        results,
    };

    match args.output {
        OutputFormat::Json => {
            serde_json::to_writer_pretty(std::io::stdout(), &output).into_diagnostic()?;
            println!();
        }
        OutputFormat::Table => {
            print_table(&output);
        }
    }
    Ok(())
}

fn print_table(output: &BenchmarkOutput) {
    use std::collections::BTreeMap;

    println!(
        "Cedar {} | {} ({} CPUs, {} MB RAM)",
        output.cedar_version,
        output.system.cpu_model,
        output.system.cpu_count,
        output.system.memory_mb
    );

    let bench_w = output
        .results
        .iter()
        .map(|r| r.benchmark.len())
        .max()
        .unwrap_or(9)
        .max(9);

    // Group results by target, preserving insertion order via BTreeMap isn't ideal
    // but we use IndexMap-style: collect targets in order seen
    let mut targets: Vec<&str> = Vec::new();
    let mut grouped: BTreeMap<&str, Vec<&BenchmarkResult>> = BTreeMap::new();
    for r in &output.results {
        if !targets.contains(&r.target.as_str()) {
            targets.push(&r.target);
        }
        grouped.entry(&r.target).or_default().push(r);
    }

    for target in &targets {
        let results = &grouped[target];
        println!();
        println!("  {}", target);
        println!(
            "  {:<bench_w$} {:>12} {:>9} {:>9} {:>9}",
            "Benchmark", "avg ± stddev", "min", "max", "p99"
        );
        println!("  {}", "-".repeat(bench_w + 12 + 3 * 10));
        for r in results {
            println!(
                "  {:<bench_w$} {:>5}µs ± {:<4} {:>7}µs {:>7}µs {:>7}µs",
                r.benchmark, r.average, format!("{:.0}", r.stddev), r.min, r.max, r.p99
            );
        }
    }

    println!();
    println!(
        "All times in microseconds ({} trials each)",
        output.results.first().map_or(0, |r| r.trials)
    );
}
