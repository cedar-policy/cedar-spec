"""Focused tests for the CI fuzz-smoke gate."""

import subprocess
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

import smoke_fuzz as smoke


class SmokeTests(unittest.TestCase):
    def test_target_discovery(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            (root / "fuzz").mkdir()
            manifest = root / "fuzz/Cargo.toml"
            manifest.write_text('[[bin]]\nname="first"\n[[bin]]\nname="second"\n')
            with patch.object(smoke, "DRT", root), patch.object(
                smoke.subprocess, "run",
                return_value=subprocess.CompletedProcess([], 0, "first\nsecond\n", ""),
            ):
                self.assertEqual(smoke.targets(), ["first", "second"])
                manifest.write_text('[[bin]]\nname="first"\n[[bin]]\nname="first"\n')
                with self.assertRaises(ValueError):
                    smoke.targets()
                manifest.write_text('[[bin]]\nname="first"\n[[bin]]\nname="second"\n')
                with patch.object(smoke.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "first\n", "")):
                    with self.assertRaises(ValueError):
                        smoke.targets()

    def test_exit_and_execution_count(self):
        with patch.object(smoke, "environment", return_value={}):
            for code, output, succeeds in (
                (0, "Done 8 runs in 0 second(s)", True),
                (0, "Done 7 runs in 0 second(s)", False),
                (1, "Done 8 runs in 0 second(s)", False),
                (0, "note: Done 8 runs in 0 second(s)", False),
                (0, "misconfigured target", False),
            ):
                with self.subTest(code=code, output=output), patch.object(
                    smoke.subprocess, "run",
                    return_value=subprocess.CompletedProcess([], code, "", output),
                ):
                    if succeeds:
                        smoke.run_target("test")
                    else:
                        with self.assertRaises(RuntimeError):
                            smoke.run_target("test")

    def test_timeout_and_flags(self):
        with patch.object(smoke, "environment", return_value={}), patch.object(
            smoke.subprocess, "run", return_value=subprocess.CompletedProcess([], 0, "", "Done 8 runs in 0 second(s)"),
        ) as invoke:
            smoke.run_target("test", 12)
            cmd = invoke.call_args.args[0]
            self.assertEqual(cmd[:3], ["timeout", "--kill-after=5s", "12s"])
            self.assertIn("--all-features", cmd)
            self.assertIn("-runs=8", cmd)
            self.assertEqual(invoke.call_args.kwargs["timeout"], 22)

    def test_input_generation_requires_fixtures(self):
        with tempfile.TemporaryDirectory() as tmp:
            with patch.object(smoke, "DRT", Path(tmp) / "cedar-drt"):
                with self.assertRaises(FileNotFoundError):
                    smoke.environment("input-generation")

    def test_suite_failure_and_budget(self):
        with patch.object(smoke, "targets", return_value=["a", "b"]), patch.object(
            smoke, "run_target", side_effect=[None, RuntimeError("crash")],
        ) as runner:
            self.assertEqual(smoke.main(), 1)
            self.assertEqual(runner.call_count, 2)
        with patch.object(smoke, "targets", return_value=["a"]), patch.object(
            smoke.time, "monotonic", side_effect=[0, 901]
        ), patch.object(smoke, "run_target") as runner:
            self.assertEqual(smoke.main(), 1)
            runner.assert_not_called()


if __name__ == "__main__":
    unittest.main()

