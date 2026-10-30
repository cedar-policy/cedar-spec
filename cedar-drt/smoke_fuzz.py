#!/usr/bin/env python3
"""Briefly exercise every Cedar fuzz target before merging changes."""

import os
import re
import subprocess
import sys
import time
from pathlib import Path

DRT = Path(__file__).resolve().parent
RUNS = 8
SUITE_SECONDS = 900
DONE = re.compile(r"^[ \t]*Done (\d+) runs? in\b", re.MULTILINE)


def targets():
    """Use cargo-fuzz as the source of truth for the target set."""
    listed = subprocess.run(
        ["cargo", "fuzz", "list"], cwd=DRT, capture_output=True,
        text=True, check=True, timeout=45,
    ).stdout.splitlines()
    if not listed:
        raise ValueError("cargo fuzz reported no targets")
    return sorted(listed)


def environment(name):
    env = os.environ.copy()
    if name == "input-generation":
        sample = DRT.parent / "cedar/cedar-policy-cli/sample-data/sandbox_a"
        for var, filename in (
            ("CEDAR_SCHEMA_FILE", "schema.cedarschema"),
            ("CEDAR_POLICY_FILE", "policies_1.cedar"),
        ):
            path = sample / filename
            if not path.is_file():
                raise FileNotFoundError(path)
            env[var] = str(path)
    return env


def run_target(name, seconds=60):
    command = [
        "timeout", "--kill-after=5s", f"{seconds}s", "cargo", "fuzz", "run",
        "-s", "none", "--all-features", name, "--", f"-runs={RUNS}",
        "-timeout=10", "-rss_limit_mb=2048", "-len_control=0",
    ]
    result = subprocess.run(
        command, cwd=DRT, env=environment(name), capture_output=True,
        text=True, errors="replace", timeout=seconds + 10,
    )
    output = result.stdout + "\n" + result.stderr
    runs = DONE.findall(output)
    if result.returncode or not runs or int(runs[-1]) < RUNS:
        raise RuntimeError(
            f"{name}: exit={result.returncode}, reported_runs={runs[-1] if runs else 0}\n"
            + "\n".join(output.splitlines()[-25:])
        )


def main():
    deadline = time.monotonic() + SUITE_SECONDS
    try:
        names = targets()
        print(f"Smoke-testing all {len(names)} declared targets", flush=True)
        for index, name in enumerate(names, 1):
            seconds = min(60, int(deadline - time.monotonic()))
            if seconds < 1:
                raise RuntimeError("Smoke suite exhausted its 900-second budget")
            run_target(name, seconds)
            print(f"[{index}/{len(names)}] PASS {name}", flush=True)
    except (OSError, ValueError, RuntimeError, subprocess.SubprocessError, KeyError) as exc:
        print(f"Fuzz smoke failed: {exc}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
