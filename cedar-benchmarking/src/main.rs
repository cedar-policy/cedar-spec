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

mod compare;
mod executor;
mod output;
pub mod request;
mod tasks;

use clap::{Parser, ValueEnum};
use miette::IntoDiagnostic;
use output::{BenchmarkOutput, BenchmarkResult, SystemInfo};
use std::path::{Path, PathBuf};
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
    /// Path to the benchmark corpus (tasks.json). Mutually exclusive with --baseline.
    #[arg(short, long, conflicts_with = "baseline")]
    corpus: Option<PathBuf>,

    /// Load "current" results from a previous JSON output file instead of running
    /// benchmarks. Mutually exclusive with --corpus. Requires --compare.
    #[arg(long, conflicts_with = "corpus", requires = "compare")]
    baseline: Option<PathBuf>,

    /// Only run specific targets (comma-separated). Only valid with --corpus.
    #[arg(short, long, value_delimiter = ',', requires = "corpus")]
    targets: Option<Vec<Target>>,

    /// Number of trials per benchmark. Ignored in --baseline mode.
    #[arg(long, default_value = "1000")]
    trials: usize,

    /// Output format
    #[arg(short, long, value_enum, default_value = "json")]
    output: OutputFormat,

    /// Compare results against previous run(s) (JSON output files)
    #[arg(long, value_name = "FILE", num_args = 1..)]
    compare: Option<Vec<PathBuf>>,

    /// Disable colored output
    #[arg(long)]
    no_color: bool,

    /// Exit non-zero if any benchmark's average regresses beyond this percentage.
    /// Requires --compare.
    #[arg(long, value_name = "PERCENT", requires = "compare")]
    regression_threshold: Option<f64>,
}

fn main() -> miette::Result<()> {
    let args = Args::parse();

    if args.corpus.is_none() && args.baseline.is_none() {
        return Err(miette::miette!(
            "Either --corpus or --baseline must be provided"
        ));
    }

    let output = if let Some(ref corpus) = args.corpus {
        run_benchmarks(corpus, args.targets.as_deref(), args.trials)?
    } else {
        // --baseline is guaranteed present by the validation above
        compare::load_baseline(args.baseline.as_ref().expect("validated above"))?
    };

    // Print benchmark results when running benchmarks directly (not in
    // baseline-only mode). In JSON mode, skip this when --compare is active to
    // avoid emitting two separate JSON documents on stdout.
    if args.corpus.is_some() {
        match args.output {
            OutputFormat::Json if args.compare.is_none() => {
                serde_json::to_writer_pretty(std::io::stdout(), &output).into_diagnostic()?;
                println!();
            }
            OutputFormat::Table => {
                print_table(&output);
            }
            _ => {}
        }
    }

    // Comparison mode
    if let Some(ref compare_paths) = args.compare {
        let reports: Vec<compare::ComparisonReport> = compare_paths
            .iter()
            .map(|path| {
                let baseline = compare::load_baseline(path)?;
                Ok(compare::compare(&output, &baseline, path))
            })
            .collect::<miette::Result<_>>()?;

        // Use the user-provided threshold for both the table marker and the
        // exit-code gate, defaulting to 5% for the table marker.
        let threshold = args.regression_threshold.unwrap_or(5.0);

        match args.output {
            OutputFormat::Table => {
                compare::print_comparison_table(&reports, !args.no_color, threshold);
            }
            OutputFormat::Json => compare::print_comparison_json(&reports)?,
        }

        if args.regression_threshold.is_some() && compare::has_regression(&reports, threshold) {
            std::process::exit(1);
        }
    }

    Ok(())
}

fn run_benchmarks(
    corpus: &Path,
    targets: Option<&[Target]>,
    trials: usize,
) -> miette::Result<BenchmarkOutput> {
    let tasks = tasks::load_corpus(corpus, targets)?;
    let exec = executor::BenchmarkExecutor::new(trials);
    let mut results = Vec::new();

    for task in tasks {
        for bench_task in task.into_benchmark_tasks()? {
            let (target, name, timing) = exec.run(&bench_task)?;
            results.push(BenchmarkResult {
                benchmark: name,
                target: target.to_string(),
                trials,
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

    Ok(BenchmarkOutput {
        cedar_version: cedar_policy::get_sdk_version().to_string(),
        system: SystemInfo::collect(),
        results,
    })
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
                r.benchmark,
                r.average,
                format!("{:.0}", r.stddev),
                r.min,
                r.max,
                r.p99
            );
        }
    }

    println!();
    println!(
        "All times in microseconds ({} trials each)",
        output.results.first().map_or(0, |r| r.trials)
    );
}
