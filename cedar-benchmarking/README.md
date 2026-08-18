# Cedar Benchmarking

A command-line tool for benchmarking the [Cedar](https://www.cedarpolicy.com/) policy language. It measures the performance of core Cedar operations (parsing, validation, authorization) across a corpus of policy sets and schemas, outputting structured JSON results.
You can use your own set of benchmarks, or test on the provided one in `corpus/`, for example:

```bash
cargo run --release -- --corpus corpus/tasks.json --trials 500 --output table
```
To use your own benchmarks, provide a path to a `tasks.json` describing your benchmarks (see [corpus format](#corpus-format)).
To install from source, run `cargo install --path .`.

### Options

| Flag                           | Description                                                                                                                                      |
| ------------------------------ | ------------------------------------------------------------------------------------------------------------------------------------------------ |
| `--corpus <path>`              | Path to a `tasks.json` file defining the benchmark corpus. Mutually exclusive with `--baseline`.                                                 |
| `--baseline <path>`            | Load "current" results from a previous JSON output file instead of running benchmarks. Mutually exclusive with `--corpus`. Requires `--compare`. |
| `--targets <list>`             | Comma-separated list of targets to run (optional, runs all by default). Only valid with `--corpus`.                                              |
| `--trials <n>`                 | Number of iterations per benchmark (default: 1000). Only valid with `--corpus`.                                                                  |
| `--output <format>`            | Output format: `json` (default) or `table` (human-readable)                                                                                      |
| `--compare <files...>`         | One or more baseline JSON files to compare against                                                                                               |
| `--no-color`                   | Disable colored output in comparison tables                                                                                                      |
| `--regression-threshold <pct>` | Exit non-zero if any benchmark's average regresses beyond this percentage. Requires `--compare`.                                                 |

### Example: run only parsing benchmarks with 500 trials


```bash
cedar-benchmarking --corpus corpus/tasks.json --targets policy_parse,schema_parse --trials 500
```

## Output format

Results are printed as JSON to stdout by default:

```json
{
  "cedar_version": "4.11.0",
  "system": {
    "cpu_model": "Intel Xeon Platinum 8275CL",
    "cpu_count": 8,
    "memory_mb": 16384
  },
  "results": [
    {
      "benchmark": "oopsla/tinytodo",
      "target": "authorization",
      "trials": 1000,
      "unit": "microseconds",
      "average": 142,
      "min": 128,
      "max": 312,
      "stddev": 18.4,
      "iqr": 12,
      "p50": 138,
      "p95": 165,
      "p99": 201
    }
  ]
}
```
but you can also print them as a table with `--output table`:
```
Cedar <version> | <hardware information>

  policy_parse
  Benchmark                   avg ± stddev       min       max       p99
  ---------------------------------------------------------------------
  tinytodo                       93µs ± 4         92µs     159µs     108µs
  oopsla/tinytodo                93µs ± 2         92µs     110µs     105µs
  oopsla/gdrive                  97µs ± 2         96µs     117µs     109µs
  oopsla/github                 115µs ± 2        113µs     130µs     126µs
[more lines...]
```

### Fields
Each `results` object in the JSON output has the following fields:

| Field         | Description                                               |
| ------------- | --------------------------------------------------------- |
| `average`     | Arithmetic mean across all trials                         |
| `min` / `max` | Fastest and slowest trial                                 |
| `stddev`      | Standard deviation (lower = more consistent)              |
| `iqr`         | Interquartile range (p75 - p25), robust measure of spread |
| `p50`         | Median latency                                            |
| `p95` / `p99` | Tail latencies                                            |

## Benchmark targets

| Target                        | Description                                                            |
| ----------------------------- | ---------------------------------------------------------------------- |
| `policy_parse`                | Parse Cedar policy text                                                |
| `json_policy_parse`           | Parse policies from JSON representation                                |
| `protobuf_policy_parse`       | Parse policies from protobuf encoding                                  |
| `schema_parse`                | Parse Cedar schema text                                                |
| `json_schema_parse`           | Parse schema from JSON representation                                  |
| `protobuf_schema_parse`       | Parse schema from protobuf encoding                                    |
| `validation`                  | Validate policies against a schema                                     |
| `authorization`               | Run authorization requests                                             |
| `entity_parse_with_schema`    | Parse entities with schema validation                                  |
| `entity_parse_without_schema` | Parse entities without schema                                          |
| `protobuf_entity_parse`       | Parse entities from protobuf encoding                                  |
| `incremental_entities`        | Incrementally add entities (measures transitive closure recomputation) |

## Corpus format

A corpus is a `tasks.json` file alongside the referenced policy/schema/entity files. Each task specifies which files to use; available targets are automatically determined from the files present.

```json
[
  {
    "name": "my-benchmark",
    "policy_file": "path/to/policies.cedar",
    "cedar_schema_file": "path/to/schema.cedarschema",
    "json_schema_file": "path/to/schema.cedarschema.json",
    "entities_file": "path/to/entities.json",
    "only_targets": ["policy_parse", "validation"]
  }
]
```

Use `only_targets` to run specific targets, or `exclude_targets` to skip specific targets. If both are set, `only_targets` is applied first and `exclude_targets` filters the result.

All paths are relative to the directory containing `tasks.json`.

## Comparing versions

To compare performance across Cedar releases, build the benchmark binary from each release and run against the same corpus:

```bash
# Build from release tags
git checkout cedar-benchmarking-v4.10.0 && cargo build --release -p cedar-benchmarking
cp target/release/cedar-benchmarking cedar-bench-4.10

git checkout cedar-benchmarking-v4.11.0 && cargo build --release -p cedar-benchmarking
cp target/release/cedar-benchmarking cedar-bench-4.11

# Run against same corpus, use compare to compare
./cedar-bench-4.10 --corpus corpus/tasks.json > results-4.10.json
./cedar-bench-4.11 --corpus corpus/tasks.json --compare results-4.10.json
```

## Comparing results

Use `--compare` to compare against one or more previous JSON outputs. Benchmarks are matched by `(name, target)` pair; unmatched entries are reported separately.

```bash
# Compare a live run against saved baselines
cedar-benchmarking --corpus corpus/tasks.json --compare results-4.10.json results-4.9.json

# Compare two saved results without re-running
cedar-benchmarking --baseline results-4.11.json --compare results-4.10.json

# CI gate: exit non-zero if any benchmark significantly regresses
cedar-benchmarking --corpus corpus/tasks.json --compare baseline.json --regression-threshold 5
```

Comparison output respects `--output`: JSON by default, or a colored table with `--output table`. Use `--no-color` to disable ANSI colors.

### Regression detection

A benchmark is flagged as a regression only when **all three** conditions are met:

1. The average latency increased by more than the threshold percentage (default 5%).
2. The absolute delta exceeds 10µs (filters out noise on very fast benchmarks).
3. The absolute delta exceeds 2× the pooled standard deviation (`√(σ_baseline² + σ_current²)`), which accounts for variance in both runs.

This prevents false positives from tiny benchmarks (e.g., 15µs → 16µs = +6.7% but only 1µs absolute) and from high-variance benchmarks where the change is within expected noise.
