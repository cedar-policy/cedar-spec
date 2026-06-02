#!/usr/bin/env python3
"""
Fuzz manager: run multiple cargo-fuzz targets in parallel with a live terminal dashboard.
"""

import argparse
import asyncio
import fnmatch
import os
import re
import signal
import sys
import time
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path

# ─── ANSI helpers ────────────────────────────────────────────────────────────

RESET = "\033[0m"
BOLD = "\033[1m"
DIM = "\033[2m"
RED = "\033[31m"
GREEN = "\033[32m"
YELLOW = "\033[33m"
BLUE = "\033[34m"
CYAN = "\033[36m"
WHITE = "\033[37m"
BG_RED = "\033[41m"

CLEAR_SCREEN = "\033[2J\033[H"
HIDE_CURSOR = "\033[?25l"
SHOW_CURSOR = "\033[?25h"


# ─── Data ────────────────────────────────────────────────────────────────────

@dataclass
class FuzzStats:
    runs: int = 0
    cov: int = 0
    ft: int = 0
    corp: str = ""
    exec_s: int = 0
    rss: str = ""
    status: str = "starting"  # starting, building, running, done, error
    start_time: float = field(default_factory=time.time)
    last_line: str = ""
    report_path: str = ""
    cov_history: list = field(default_factory=list)  # (timestamp, cov) samples


# ─── Parsing ─────────────────────────────────────────────────────────────────

STAT_RE = re.compile(
    r"#(\d+)\s+\w+\s+cov:\s*(\d+)\s+ft:\s*(\d+)\s+corp:\s*(\S+)\s+"
    r".*?exec/s:\s*(\d+)\s+rss:\s*(\S+)"
)
DONE_RE = re.compile(r"Done (\d+) runs in (\d+) second")


def parse_line(line: str, stats: FuzzStats):
    if "Compiling" in line or "Downloading" in line:
        stats.status = "building"
        return
    m = STAT_RE.search(line)
    if m:
        stats.status = "running"
        stats.runs = int(m.group(1))
        stats.cov = int(m.group(2))
        stats.ft = int(m.group(3))
        stats.corp = m.group(4)
        stats.exec_s = int(m.group(5))
        stats.rss = m.group(6)
        return
    m = DONE_RE.search(line)
    if m:
        stats.runs = int(m.group(1))
        stats.status = "done"
        return
    stats.last_line = line.strip()


# ─── Display ─────────────────────────────────────────────────────────────────

STATUS_ICONS = {
    "starting": f"{YELLOW}◌{RESET}",
    "building": f"{BLUE}⚙{RESET}",
    "running": f"{GREEN}●{RESET}",
    "done": f"{DIM}✓{RESET}",
    "error": f"{RED}✗{RESET}",
}


def format_elapsed(start: float) -> str:
    elapsed = int(time.time() - start)
    m, s = divmod(elapsed, 60)
    h, m = divmod(m, 60)
    if h:
        return f"{h}h{m:02d}m"
    if m:
        return f"{m}m{s:02d}s"
    return f"{s}s"


def cov_delta(stats: FuzzStats) -> str:
    """Compute cov % change: current vs average of samples from 10-20s ago."""
    now = time.time()
    history = stats.cov_history
    # Get samples from 10-20s ago
    old_samples = [cov for t, cov in history if now - 20 <= t <= now - 10]
    if not old_samples:
        text, color = "—", DIM
    else:
        avg_old = sum(old_samples) / len(old_samples)
        if avg_old == 0:
            text, color = ("+∞", GREEN) if stats.cov > 0 else ("—", DIM)
        else:
            pct = ((stats.cov - avg_old) / avg_old) * 100
            if pct <= 0:
                text, color = "+0%", DIM
            elif pct >= 1:
                text, color = f"+{pct:.0f}%", GREEN
            else:
                text, color = f"+{pct:.1f}%", DIM
    return f"{color}{text:>6}{RESET}"


ORANGE = "\033[38;5;208m"


def heat_color(value: int, max_value: int) -> str:
    """Color a value based on its ratio to the max across all targets."""
    if max_value == 0:
        return WHITE
    ratio = value / max_value
    if ratio >= 0.8:
        return GREEN
    if ratio >= 0.5:
        return WHITE
    if ratio >= 0.3:
        return YELLOW
    if ratio >= 0.1:
        return ORANGE
    return RED


def colorized(value: int, max_value: int, width: int, fmt: str = ",") -> str:
    color = heat_color(value, max_value)
    return f"{color}{value:{fmt}}{RESET}".rjust(width + len(color) + len(RESET))


def render(targets: dict[str, FuzzStats], term_width: int):
    # Compute maxes across active/done targets
    active_stats = [s for s in targets.values() if s.status in ("running", "done")]
    max_runs = max((s.runs for s in active_stats), default=0)
    max_cov = max((s.cov for s in active_stats), default=0)
    max_ft = max((s.ft for s in active_stats), default=0)
    max_exec = max((s.exec_s for s in active_stats), default=0)

    tw = max(len(name) for name in targets) + 2  # target column width

    lines = []
    lines.append(f"{BOLD}{'═' * term_width}{RESET}")
    lines.append(f"{BOLD} 🔥 Fuzz Manager{RESET}  {DIM}{datetime.now().strftime('%H:%M:%S')}{RESET}")
    lines.append(f"{BOLD}{'─' * term_width}{RESET}")

    # Header
    lines.append(
        f"  {'Target':<{tw}} {'Status':<10} {'Runs':>10} {'Cov':>6} {'Δcov':>6} "
        f"{'Feat':>6} {'exec/s':>8} {'Time':>7}"
    )
    lines.append(f"  {'─' * (term_width - 4)}")

    for name, st in targets.items():
        icon = STATUS_ICONS.get(st.status, "?")
        elapsed = format_elapsed(st.start_time)
        pad = tw - 2  # account for icon + space

        if st.status == "error":
            detail = f"{RED}{st.report_path}{RESET}" if st.report_path else f"{RED}failed{RESET}"
            lines.append(f"  {icon} {name:<{pad}} {detail}")
        elif st.status in ("starting", "building"):
            label = "building…" if st.status == "building" else "starting…"
            lines.append(f"  {icon} {name:<{pad}} {DIM}{label:<10}{RESET} {'':>10} {'':>6} {'':>6} {'':>6} {'':>8} {elapsed:>7}")
        elif st.status == "done":
            runs_s = colorized(st.runs, max_runs, 10)
            cov_s = colorized(st.cov, max_cov, 6)
            ft_s = colorized(st.ft, max_ft, 6)
            delta = cov_delta(st)
            lines.append(
                f"  {icon} {name:<{pad}} {DIM}{'done':<10}{RESET} {runs_s} {cov_s} {delta} "
                f"{ft_s} {DIM}{'—':>8}{RESET} {elapsed:>7}"
            )
        else:
            runs_s = colorized(st.runs, max_runs, 10)
            cov_s = colorized(st.cov, max_cov, 6)
            ft_s = colorized(st.ft, max_ft, 6)
            exec_s = colorized(st.exec_s, max_exec, 8)
            delta = cov_delta(st)
            lines.append(
                f"  {icon} {name:<{pad}} {'running':<10} {runs_s} {cov_s} {delta} "
                f"{ft_s} {exec_s} {elapsed:>7}"
            )

    lines.append(f"{BOLD}{'═' * term_width}{RESET}")

    active = sum(1 for s in targets.values() if s.status in ("starting", "building", "running"))
    done = sum(1 for s in targets.values() if s.status == "done")
    errors = sum(1 for s in targets.values() if s.status == "error")
    lines.append(f"  {GREEN}▶ {active} active{RESET}  {DIM}✓ {done} done{RESET}  {RED}✗ {errors} errors{RESET}")

    return "\n".join(lines)


# ─── Runner ──────────────────────────────────────────────────────────────────

async def run_target(
    name: str, stats: FuzzStats, timeout: int | None, reports_dir: Path, sanitizer: str
):
    cmd = ["cargo", "fuzz", "run", "-s", sanitizer, name, "--"]
    if timeout:
        cmd.append(f"-max_total_time={timeout}")

    proc = await asyncio.create_subprocess_exec(
        *cmd,
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.STDOUT,
        cwd=str(Path(__file__).parent),
    )

    output_lines: list[str] = []
    assert proc.stdout is not None
    while True:
        line = await proc.stdout.readline()
        if not line:
            break
        decoded = line.decode("utf-8", errors="replace")
        output_lines.append(decoded)
        parse_line(decoded, stats)

    await proc.wait()

    if proc.returncode != 0 and stats.status != "done":
        stats.status = "error"
        report_path = reports_dir / f"{name}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.txt"
        report_path.write_text("".join(output_lines))
        stats.report_path = str(report_path)
    elif stats.status != "error":
        stats.status = "done"


async def display_loop(targets: dict[str, FuzzStats]):
    try:
        term_width = os.get_terminal_size().columns
    except OSError:
        term_width = 100

    sys.stdout.write(HIDE_CURSOR)
    last_sample = 0.0
    try:
        while True:
            now = time.time()
            # Sample coverage every second
            if now - last_sample >= 1.0:
                last_sample = now
                for st in targets.values():
                    if st.status in ("running", "done"):
                        st.cov_history.append((now, st.cov))
                        # Prune samples older than 25s
                        st.cov_history = [(t, c) for t, c in st.cov_history if now - t <= 25]
            sys.stdout.write(CLEAR_SCREEN)
            sys.stdout.write(render(targets, term_width))
            sys.stdout.flush()
            await asyncio.sleep(0.5)
    except asyncio.CancelledError:
        pass
    finally:
        sys.stdout.write(SHOW_CURSOR)
        sys.stdout.flush()


async def main():
    parser = argparse.ArgumentParser(description="Run multiple fuzz targets in parallel")
    parser.add_argument(
        "--matching", required=True, help="Glob pattern to match target names (e.g. 'protobuf-*')"
    )
    parser.add_argument("--timeout", type=int, default=None, help="Max seconds per target")
    parser.add_argument(
        "--sanitizer", "-s", default="none", help="Sanitizer to use (default: none)"
    )
    parser.add_argument("--jobs", "-j", type=int, default=None, help="Max parallel targets")
    args = parser.parse_args()

    # Get target list
    proc = await asyncio.create_subprocess_exec(
        "cargo", "fuzz", "list",
        stdout=asyncio.subprocess.PIPE,
        stderr=asyncio.subprocess.PIPE,
        cwd=str(Path(__file__).parent),
    )
    stdout, _ = await proc.communicate()
    all_targets = stdout.decode().strip().splitlines()

    matched = [t for t in all_targets if fnmatch.fnmatch(t, args.matching)]
    if not matched:
        print(f"{RED}No targets matching '{args.matching}'{RESET}")
        print(f"Available: {', '.join(all_targets[:10])}...")
        sys.exit(1)

    print(f"Matched {len(matched)} targets: {', '.join(matched)}")

    # Pre-build all targets to avoid cargo lock contention during parallel runs
    print(f"Pre-building {len(matched)} targets...")
    for name in matched:
        build_proc = await asyncio.create_subprocess_exec(
            "cargo", "fuzz", "build", "-s", args.sanitizer, name,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.STDOUT,
            cwd=str(Path(__file__).parent),
        )
        await build_proc.wait()
        if build_proc.returncode != 0:
            print(f"{RED}Failed to build target '{name}'{RESET}")
            sys.exit(1)
    print(f"{GREEN}Build complete.{RESET}")

    reports_dir = Path(__file__).parent / "fuzz_reports"
    reports_dir.mkdir(exist_ok=True)

    targets: dict[str, FuzzStats] = {name: FuzzStats() for name in matched}

    # Semaphore for concurrency limit
    sem = asyncio.Semaphore(args.jobs or len(matched))

    async def run_with_sem(name: str, stats: FuzzStats):
        async with sem:
            await run_target(name, stats, args.timeout, reports_dir, args.sanitizer)

    display_task = asyncio.create_task(display_loop(targets))
    fuzz_tasks = [asyncio.create_task(run_with_sem(n, s)) for n, s in targets.items()]

    # Handle Ctrl+C gracefully
    loop = asyncio.get_event_loop()
    stop_event = asyncio.Event()

    def handle_signal():
        stop_event.set()
        for t in fuzz_tasks:
            t.cancel()

    for sig in (signal.SIGINT, signal.SIGTERM):
        loop.add_signal_handler(sig, handle_signal)

    await asyncio.gather(*fuzz_tasks, return_exceptions=True)
    display_task.cancel()
    await asyncio.gather(display_task, return_exceptions=True)

    # Final render
    try:
        term_width = os.get_terminal_size().columns
    except OSError:
        term_width = 100
    sys.stdout.write(CLEAR_SCREEN)
    sys.stdout.write(render(targets, term_width))
    sys.stdout.write("\n\n")
    sys.stdout.flush()

    # Summary of errors
    errors = {n: s for n, s in targets.items() if s.status == "error"}
    if errors:
        print(f"\n{RED}{BOLD}Errors ({len(errors)}):{RESET}")
        for name, st in errors.items():
            print(f"  ✗ {name}: {st.report_path}")
        sys.exit(1)


if __name__ == "__main__":
    asyncio.run(main())
