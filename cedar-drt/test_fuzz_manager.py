"""Verify cancellation stops a fuzz subprocess group, including descendants."""

import asyncio
import os
import signal
import sys
import unittest
from pathlib import Path
from unittest.mock import patch

import fuzz_manager


class GroupCleanupTests(unittest.IsolatedAsyncioTestCase):
    async def test_terminate_group_escalates_if_parent_stalls(self):
        class Stalled:
            pid = 42
            async def wait(self):
                return None
        async def timeout(awaitable, **kwargs):
            awaitable.close()
            raise asyncio.TimeoutError
        with patch.object(fuzz_manager.os, "killpg") as killpg, patch.object(
            fuzz_manager.asyncio, "wait_for", side_effect=timeout
        ):
            await fuzz_manager.terminate_process_group(Stalled())
        self.assertEqual(killpg.call_count, 2)
        self.assertEqual(killpg.call_args_list[0].args, (42, signal.SIGTERM))
        self.assertEqual(killpg.call_args_list[1].args, (42, signal.SIGKILL))

    async def test_cancelled_run_signals_process_group(self):
        class Reader:
            def __init__(self):
                self.started = asyncio.Event()
            async def readline(self):
                self.started.set()
                await asyncio.Future()
        class Pending:
            pid = 424242
            returncode = None
            def __init__(self):
                self.stdout = Reader()
            async def wait(self):
                self.returncode = -15
                return -15
        proc = Pending()
        stats = fuzz_manager.FuzzStats()
        with patch.object(fuzz_manager.asyncio, "create_subprocess_exec", return_value=proc) as spawn, patch.object(
            fuzz_manager.os, "killpg"
        ) as killpg:
            task = asyncio.create_task(fuzz_manager.run_target("t", "t", stats, 1, Path("."), "none"))
            await asyncio.wait_for(proc.stdout.started.wait(), timeout=2)
            task.cancel()
            await asyncio.wait_for(task, timeout=2)
        self.assertEqual(stats.status, "stopped")
        self.assertTrue(spawn.call_args.kwargs["start_new_session"])
        self.assertEqual(
            [call.args for call in killpg.call_args_list],
            [(proc.pid, signal.SIGTERM), (proc.pid, signal.SIGKILL)],
        )

    @unittest.skipUnless(sys.platform.startswith("linux"), "Uses Linux /proc")
    async def test_descendant_ignoring_sigterm_is_stopped(self):
        # Wait for READY to ensure the descendant installed SIG_IGN
        # before its process group receives SIGTERM.
        child_code = (
            "import signal,time; "
            "signal.signal(signal.SIGTERM, signal.SIG_IGN); "
            "print('READY', flush=True); time.sleep(30)"
        )
        parent_code = (
            "import subprocess,sys,time; "
            f"child=subprocess.Popen([sys.executable,'-u','-c',{child_code!r}], "
            "stdout=subprocess.PIPE, text=True); "
            "assert child.stdout.readline().strip() == 'READY'; "
            "print(child.pid,flush=True); time.sleep(30)"
        )
        proc = await asyncio.create_subprocess_exec(
            sys.executable, "-u", "-c", parent_code,
            start_new_session=True, stdout=asyncio.subprocess.PIPE,
        )
        assert proc.stdout is not None
        child = int(await asyncio.wait_for(proc.stdout.readline(), timeout=3))
        try:
            await fuzz_manager.terminate_process_group(proc)
            await asyncio.sleep(0.1)
            stat = Path(f"/proc/{child}/stat")
            if stat.exists():
                self.assertEqual(
                    stat.read_text().split(") ", 1)[1][0], "Z",
                    "SIGTERM-ignoring child still runs",
                )
        finally:
            try:
                os.killpg(proc.pid, signal.SIGKILL)
            except ProcessLookupError:
                pass
            if proc.returncode is None:
                await proc.wait()
            try:
                os.kill(child, signal.SIGKILL)
            except ProcessLookupError:
                pass

    @unittest.skipUnless(sys.platform.startswith("linux"), "Uses Linux /proc")
    async def test_real_group_cleans_up_descendants(self):
        script = (
            "import subprocess,sys,time; "
            "child=subprocess.Popen([sys.executable,'-c','import time;time.sleep(30)']); "
            "print(child.pid,flush=True); time.sleep(30)"
        )
        proc = await asyncio.create_subprocess_exec(
            sys.executable, "-c", script,
            start_new_session=True, stdout=asyncio.subprocess.PIPE,
        )
        assert proc.stdout is not None
        child = int(await asyncio.wait_for(proc.stdout.readline(), timeout=3))
        try:
            await fuzz_manager.terminate_process_group(proc)
            await asyncio.sleep(0.1)
            stat = Path(f"/proc/{child}/stat")
            if stat.exists():
                # A zombie is already terminated and awaits its parent/reaper.
                state = stat.read_text().split(") ", 1)[1][0]
                self.assertEqual(state, "Z", "Fuzz descendant is still running")
        finally:
            if proc.returncode is None:
                os.killpg(proc.pid, signal.SIGKILL)
                await proc.wait()
            try:
                os.kill(child, signal.SIGKILL)
            except ProcessLookupError:
                pass


if __name__ == "__main__":
    unittest.main()
