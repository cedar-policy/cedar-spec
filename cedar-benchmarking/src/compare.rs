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

use crate::output::{BenchmarkOutput, BenchmarkResult};
use miette::{Context, IntoDiagnostic};
use owo_colors::OwoColorize;
use serde::Serialize;
use std::collections::HashMap;
use std::path::Path;

/// Minimum absolute delta (in microseconds) required to consider a change
/// significant. Changes smaller than this are assumed to be measurement noise,
/// regardless of percentage. This prevents flagging tiny benchmarks (e.g.,
/// 15µs → 16µs = +6.7%) as regressions.
const MIN_DELTA_FLOOR_US: u128 = 10;

/// Number of baseline standard deviations the delta must exceed to be
/// considered statistically significant. A delta smaller than this many σ is
/// likely within normal run-to-run variance.
const SIGNIFICANCE_SIGMA: f64 = 2.0;

/// Whether a change is a significant regression, improvement, or neither.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Significance {
    Regression,
    Improvement,
    Insignificant,
}

/// A key that uniquely identifies a benchmark result.
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize)]
pub struct BenchmarkKey {
    pub benchmark: String,
    pub target: String,
}

impl BenchmarkKey {
    fn from_result(r: &BenchmarkResult) -> Self {
        Self {
            benchmark: r.benchmark.clone(),
            target: r.target.clone(),
        }
    }
}

/// Comparison data for a single benchmark that exists in both runs.
#[derive(Debug, Serialize)]
pub struct BenchmarkComparison {
    pub benchmark: String,
    pub target: String,
    pub current_avg: u128,
    pub baseline_avg: u128,
    pub delta_avg: i128,
    pub delta_avg_pct: f64,
    pub baseline_stddev: f64,
    pub current_stddev: f64,
    pub current_p50: u128,
    pub baseline_p50: u128,
    pub delta_p50_pct: f64,
    pub current_p99: u128,
    pub baseline_p99: u128,
    pub delta_p99_pct: f64,
}

impl BenchmarkComparison {
    /// Determines the significance of this comparison.
    ///
    /// A change is significant only when ALL three conditions are met:
    /// 1. The average changed by more than `threshold_pct` percent.
    /// 2. The absolute delta exceeds [`MIN_DELTA_FLOOR_US`] microseconds.
    /// 3. The absolute delta exceeds [`SIGNIFICANCE_SIGMA`] × the pooled
    ///    standard deviation (`sqrt(σ_baseline² + σ_current²)`).
    ///
    /// The pooled standard deviation accounts for variance in both runs,
    /// preventing false positives when either run is noisy.
    ///
    /// This avoids false positives from:
    /// - Tiny benchmarks where a 1µs jitter causes a large percentage swing.
    /// - High-variance benchmarks where the change is within normal noise.
    fn significance(&self, threshold_pct: f64) -> Significance {
        let abs_delta = self.delta_avg.unsigned_abs();
        if abs_delta < MIN_DELTA_FLOOR_US {
            return Significance::Insignificant;
        }
        let pooled_sigma = self.baseline_stddev.hypot(self.current_stddev);
        if abs_delta as f64 <= SIGNIFICANCE_SIGMA * pooled_sigma {
            return Significance::Insignificant;
        }
        if self.delta_avg_pct > threshold_pct {
            Significance::Regression
        } else if self.delta_avg_pct < -threshold_pct {
            Significance::Improvement
        } else {
            Significance::Insignificant
        }
    }
}

/// Full comparison report between current results and one baseline.
#[derive(Debug, Serialize)]
pub struct ComparisonReport {
    pub baseline_file: String,
    pub baseline_cedar_version: String,
    pub current_cedar_version: String,
    pub matched: Vec<BenchmarkComparison>,
    pub only_in_current: Vec<BenchmarkKey>,
    pub only_in_baseline: Vec<BenchmarkKey>,
}

/// Load a baseline JSON file.
pub fn load_baseline(path: &Path) -> miette::Result<BenchmarkOutput> {
    let file = std::fs::File::open(path)
        .into_diagnostic()
        .wrap_err(format!("Failed to open baseline file '{}'", path.display()))?;
    serde_json::from_reader(file)
        .into_diagnostic()
        .wrap_err(format!(
            "Failed to parse baseline file '{}'",
            path.display()
        ))
}

/// Compare current results against a baseline, producing a report.
pub fn compare(
    current: &BenchmarkOutput,
    baseline: &BenchmarkOutput,
    baseline_path: &Path,
) -> ComparisonReport {
    let baseline_map: HashMap<BenchmarkKey, &BenchmarkResult> = baseline
        .results
        .iter()
        .map(|r| (BenchmarkKey::from_result(r), r))
        .collect();

    let current_map: HashMap<BenchmarkKey, &BenchmarkResult> = current
        .results
        .iter()
        .map(|r| (BenchmarkKey::from_result(r), r))
        .collect();

    let mut matched = Vec::new();
    let mut only_in_current = Vec::new();

    for result in &current.results {
        let key = BenchmarkKey::from_result(result);
        if let Some(baseline_result) = baseline_map.get(&key) {
            matched.push(compute_comparison(result, baseline_result));
        } else {
            only_in_current.push(key);
        }
    }

    let only_in_baseline: Vec<BenchmarkKey> = baseline_map
        .keys()
        .filter(|k| !current_map.contains_key(k))
        .cloned()
        .collect();

    ComparisonReport {
        baseline_file: baseline_path.display().to_string(),
        baseline_cedar_version: baseline.cedar_version.clone(),
        current_cedar_version: current.cedar_version.clone(),
        matched,
        only_in_current,
        only_in_baseline,
    }
}

/// Check if any benchmark in the reports represents a significant regression.
///
/// See [`BenchmarkComparison::significance`] for the criteria.
pub fn has_regression(reports: &[ComparisonReport], threshold_pct: f64) -> bool {
    reports
        .iter()
        .flat_map(|r| &r.matched)
        .any(|c| c.significance(threshold_pct) == Significance::Regression)
}

/// Print comparison reports as JSON to stdout.
pub fn print_comparison_json(reports: &[ComparisonReport]) -> miette::Result<()> {
    serde_json::to_writer_pretty(std::io::stdout(), reports).into_diagnostic()?;
    println!();
    Ok(())
}

/// Print comparison reports as a human-readable table.
pub fn print_comparison_table(reports: &[ComparisonReport], color: bool, threshold_pct: f64) {
    for report in reports {
        println!();
        println!(
            "Comparison: Cedar {} (current) vs {} (Cedar {})",
            report.current_cedar_version, report.baseline_file, report.baseline_cedar_version
        );
        println!();

        if report.matched.is_empty() {
            println!("  No matching benchmarks found.");
        } else {
            print_matched_table(&report.matched, color, threshold_pct);
        }

        print_unmatched(
            "Benchmarks only in current run (no baseline)",
            &report.only_in_current,
        );
        print_unmatched(
            "Benchmarks only in baseline (not run)",
            &report.only_in_baseline,
        );

        println!();
    }
}

fn print_matched_table(matched: &[BenchmarkComparison], color: bool, threshold_pct: f64) {
    let bench_w = matched
        .iter()
        .map(|c| c.benchmark.len())
        .max()
        .unwrap_or(9)
        .max(9);

    // Group by target, preserving insertion order
    let mut targets: Vec<&str> = Vec::new();
    let mut grouped: Vec<(&str, Vec<&BenchmarkComparison>)> = Vec::new();
    for c in matched {
        if let Some(pos) = targets.iter().position(|&t| t == c.target) {
            grouped[pos].1.push(c);
        } else {
            targets.push(&c.target);
            grouped.push((&c.target, vec![c]));
        }
    }

    let separator = "-".repeat(bench_w + 8 + 8 + 5 + 7 + 7 + 7 + 12);

    for (target, comparisons) in &grouped {
        println!();
        println!("  {target}");
        println!(
            "  {:<bench_w$}  {:>8}  {:>8}  {:>5}  {:>7}  {:>7}  {:>7}",
            "Benchmark", "avg (µs)", "Δavg", "σ", "Δavg%", "Δp50%", "Δp99%"
        );
        println!("  {separator}");

        for c in comparisons {
            let delta_str = format_signed(c.delta_avg);
            let pooled_sigma = c.baseline_stddev.hypot(c.current_stddev);
            let sigma_str = format!("{pooled_sigma:.0}");
            let avg_pct = format_pct(c.delta_avg_pct);
            let p50_pct = format_pct(c.delta_p50_pct);
            let p99_pct = format_pct(c.delta_p99_pct);
            let significance = c.significance(threshold_pct);

            // Pad values to their column widths *before* applying color, since
            // ANSI escape codes are invisible but counted by format width specifiers.
            let avg_col = format!("{avg_pct:>7}");
            let p50_col = format!("{p50_pct:>7}");
            let p99_col = format!("{p99_pct:>7}");

            let (avg_col, p50_col, p99_col, suffix) = if color {
                match significance {
                    Significance::Regression => (
                        format!("{}", avg_col.red().bold()),
                        format!("{}", p50_col.red().bold()),
                        format!("{}", p99_col.red().bold()),
                        format!("{}", " ← REGRESSION".red().bold()),
                    ),
                    Significance::Improvement => (
                        format!("{}", avg_col.green().bold()),
                        format!("{}", p50_col.green().bold()),
                        format!("{}", p99_col.green().bold()),
                        String::new(),
                    ),
                    Significance::Insignificant => (avg_col, p50_col, p99_col, String::new()),
                }
            } else {
                let suffix = if significance == Significance::Regression {
                    " ← REGRESSION".to_string()
                } else {
                    String::new()
                };
                (avg_col, p50_col, p99_col, suffix)
            };

            println!(
                "  {:<bench_w$}  {:>8}  {:>8}  {:>5}  {}  {}  {}{}",
                c.benchmark, c.current_avg, delta_str, sigma_str, avg_col, p50_col, p99_col, suffix,
            );
        }
    }
}

fn print_unmatched(header: &str, keys: &[BenchmarkKey]) {
    if !keys.is_empty() {
        println!();
        println!("  {header}:");
        for key in keys {
            println!("    {}/{}", key.benchmark, key.target);
        }
    }
}

fn compute_comparison(
    current: &BenchmarkResult,
    baseline: &BenchmarkResult,
) -> BenchmarkComparison {
    BenchmarkComparison {
        benchmark: current.benchmark.clone(),
        target: current.target.clone(),
        current_avg: current.average,
        baseline_avg: baseline.average,
        delta_avg: current.average as i128 - baseline.average as i128,
        delta_avg_pct: pct_change(current.average, baseline.average),
        baseline_stddev: baseline.stddev,
        current_stddev: current.stddev,
        current_p50: current.p50,
        baseline_p50: baseline.p50,
        delta_p50_pct: pct_change(current.p50, baseline.p50),
        current_p99: current.p99,
        baseline_p99: baseline.p99,
        delta_p99_pct: pct_change(current.p99, baseline.p99),
    }
}

/// Compute the percentage change from `baseline` to `current`.
/// When `baseline` is 0 and `current` is non-zero, returns a large sentinel
/// value (`f64::MAX`) to ensure the change is always flagged as significant
/// while remaining JSON-serializable.
fn pct_change(current: u128, baseline: u128) -> f64 {
    if baseline == 0 {
        if current == 0 {
            0.0
        } else {
            f64::MAX
        }
    } else {
        (current as f64 - baseline as f64) / baseline as f64 * 100.0
    }
}

fn format_signed(value: i128) -> String {
    if value > 0 {
        format!("+{value}")
    } else {
        format!("{value}")
    }
}

fn format_pct(pct: f64) -> String {
    // Sentinel value from pct_change when baseline was 0
    if pct >= f64::MAX {
        "+∞%".to_string()
    } else if pct > 0.0 {
        format!("+{pct:.1}%")
    } else {
        format!("{pct:.1}%")
    }
}
