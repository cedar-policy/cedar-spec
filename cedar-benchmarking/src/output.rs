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

use serde::Serialize;
use sysinfo::{CpuRefreshKind, RefreshKind, System};

/// Top-level benchmark output format
#[derive(Debug, Serialize)]
pub struct BenchmarkOutput {
    pub cedar_version: String,
    pub system: SystemInfo,
    pub results: Vec<BenchmarkResult>,
}

/// Information about the system running the benchmarks
#[derive(Debug, Serialize)]
pub struct SystemInfo {
    pub cpu_model: String,
    pub cpu_count: usize,
    pub memory_mb: u64,
}

impl SystemInfo {
    pub fn collect() -> Self {
        let mut sys = System::new_with_specifics(
            RefreshKind::nothing().with_cpu(CpuRefreshKind::everything()),
        );
        std::thread::sleep(sysinfo::MINIMUM_CPU_UPDATE_INTERVAL);
        sys.refresh_cpu_all();
        sys.refresh_memory();

        let cpu_model = sys
            .cpus()
            .first()
            .map(|c| c.brand().to_string())
            .unwrap_or_default();

        SystemInfo {
            cpu_model,
            cpu_count: sys.cpus().len(),
            memory_mb: sys.total_memory() / (1024 * 1024),
        }
    }
}

/// A single benchmark result
#[derive(Debug, Serialize)]
pub struct BenchmarkResult {
    pub benchmark: String,
    pub target: String,
    pub trials: usize,
    pub unit: String,
    pub average: u128,
    pub min: u128,
    pub max: u128,
    pub stddev: f64,
    pub iqr: u128,
    pub p50: u128,
    pub p95: u128,
    pub p99: u128,
}

/// Timing statistics from a benchmark run
#[derive(Debug, Clone)]
pub struct TimingInfo {
    pub average: u128,
    pub min: u128,
    pub max: u128,
    pub stddev: f64,
    pub iqr: u128,
    pub p50: u128,
    pub p95: u128,
    pub p99: u128,
}

impl TimingInfo {
    pub fn from_runs(mut runs: Vec<u128>) -> Self {
        runs.sort_unstable();
        let len = runs.len();
        let average = runs.iter().sum::<u128>() / (len as u128);

        let variance = runs
            .iter()
            .map(|&x| {
                let diff = x as f64 - average as f64;
                diff * diff
            })
            .sum::<f64>()
            / (len as f64);
        let stddev = variance.sqrt();

        let p25 = runs[len * 25 / 100];
        let p75 = runs[len * 75 / 100];

        TimingInfo {
            average,
            min: runs[0],
            max: runs[len - 1],
            stddev,
            iqr: p75 - p25,
            p50: runs[len * 50 / 100],
            p95: runs[len * 95 / 100],
            p99: runs[len * 99 / 100],
        }
    }
}
