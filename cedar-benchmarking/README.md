# Cedar Benchmarking

A command-line tool for benchmarking the [Cedar](https://www.cedarpolicy.com/) policy language. It measures the performance of core Cedar operations (parsing, validation, authorization) across a corpus of policy sets and schemas, outputting structured JSON results.
You can use your own set of benchmarks, or test on the provided one in `corpus/`, for example:

```bash
cargo run --release -- --corpus corpus/tasks.json --trials 500 --output table
```
To use your own benchmarks, provide a path to a `tasks.json` describing your benchmarks.

### Options

| Flag | Description |
|------|-------------|
| `--corpus <path>` | Path to a `tasks.json` file defining the benchmark corpus (required) |
| `--targets <list>` | Comma-separated list of targets to run (optional, runs all by default) |
| `--trials <n>` | Number of iterations per benchmark (default: 1000) |
| `--output <format>` | Output format: `json` (default) or `table` (human-readable) |

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

### Fields

| Field | Description |
|-------|-------------|
| `average` | Arithmetic mean across all trials |
| `min` / `max` | Fastest and slowest trial |
| `stddev` | Standard deviation (lower = more consistent) |
| `iqr` | Interquartile range (p75 - p25), robust measure of spread |
| `p50` | Median latency |
| `p95` / `p99` | Tail latencies |

## Benchmark targets

| Target | Description |
|--------|-------------|
| `policy_parse` | Parse Cedar policy text |
| `json_policy_parse` | Parse policies from JSON representation |
| `protobuf_policy_parse` | Parse policies from protobuf encoding |
| `schema_parse` | Parse Cedar schema text |
| `json_schema_parse` | Parse schema from JSON representation |
| `protobuf_schema_parse` | Parse schema from protobuf encoding |
| `validation` | Validate policies against a schema |
| `authorization` | Run authorization requests |
| `entity_parse_with_schema` | Parse entities with schema validation |
| `entity_parse_without_schema` | Parse entities without schema |
| `protobuf_entity_parse` | Parse entities from protobuf encoding |

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
    "exclude_targets": ["protobuf_policy_parse"]
  }
]
```

All paths are relative to the directory containing `tasks.json`.

## Comparing versions

To compare performance across Cedar releases, build the benchmark binary from each release and run against the same corpus:

```bash
# Build from release tags
git checkout v4.10.0 && cargo build --release -p cedar-benchmarking
cp target/release/cedar-benchmarking cedar-bench-4.10

git checkout v4.11.0 && cargo build --release -p cedar-benchmarking
cp target/release/cedar-benchmarking cedar-bench-4.11

# Run against same corpus
./cedar-bench-4.10 --corpus corpus/tasks.json > results-4.10.json
./cedar-bench-4.11 --corpus corpus/tasks.json > results-4.11.json
```
