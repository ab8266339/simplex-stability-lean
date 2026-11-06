import os
import pathlib
import subprocess
import unittest
import uuid
from unittest.mock import patch, Mock
import verification_guards as g

BASE = pathlib.Path(__file__).resolve().parent
class GuardTests(unittest.TestCase):
    def setUp(self):
        self.root = BASE / "tests-tmp" / uuid.uuid4().hex
        self.root.mkdir(parents=True)
        self.source = self.root / "Snapshot.lean"
        self.source.write_text("theorem exact_snapshot : True := True.intro\n", encoding="utf-8")
        self.expected = g.source_sha256(self.source)
    def result(self, code=0):
        return subprocess.CompletedProcess(["lean"], code, "compiler output", "compiler errors" if code else "")
    def mathlib(self):
        repo = self.root / "mathlib"
        (repo / "Mathlib").mkdir(parents=True)
        (repo / "Mathlib.lean").write_text("import Mathlib.Init\n")
        (repo / "lakefile.toml").write_text('name = "mathlib"\n')
        (repo / "lean-toolchain").write_text("leanprover/lean4:v4.31.0\n")
        provider = repo / ".lake/build/lib/lean"
        (provider / "Mathlib").mkdir(parents=True)
        return repo,provider
    def check_env(self, version="4.31.0", head=g.EXPECTED_MATHLIB_COMMIT,
                  first_provider=None, root_override=None, git_available=True):
        repo,provider = self.mathlib()
        path = str(provider) if first_provider is None else str(first_provider)+os.pathsep+str(provider)
        env={"LEAN_PATH":path, "PATH":os.environ.get("PATH","")}
        def answer(args, **kwargs):
            if args[-1] == "--version":
                return "Lean (version "+version+", platform, commit test, Release)"
            if args[-1] == "--show-toplevel":
                return str(repo if root_override is None else root_override)
            if args[-1] == "HEAD": return head
            raise AssertionError(args)
        with patch.object(g.subprocess,"check_output",side_effect=answer), \
             patch.object(g.shutil,"which",return_value="git" if git_available else None):
            return g.verify_environment_pins("lean",env)

    def test_matching_snapshot_compiles(self):
        rec,out,err=g.compile_checked(["lean"],self.source,self.expected,{},runner=lambda *a,**k:self.result())
        self.assertEqual(rec["exit_code"],0)
        self.assertTrue(rec["source_hash_match"])
        self.assertEqual(rec["source_sha256_before"],self.expected)
        self.assertEqual(rec["source_sha256_after"],self.expected)
    def test_precompile_mutation_never_runs_compiler(self):
        self.source.write_text("changed")
        runner=Mock()
        rec,_,_=g.compile_checked(["lean"],self.source,self.expected,{},runner=runner)
        runner.assert_not_called()
        self.assertEqual(rec["exit_code"],125)
        self.assertFalse(rec["compiler_ran"])
    def test_postcompile_mutation_rejects_successful_compiler(self):
        def run(*a,**k):
            self.source.write_text("changed during compile")
            return self.result()
        rec,_,_=g.compile_checked(["lean"],self.source,self.expected,{},runner=run)
        self.assertEqual(rec["compiler_exit_code"],0)
        self.assertEqual(rec["exit_code"],125)
        self.assertFalse(rec["source_hash_match"])
    def test_deleted_snapshot_rejects_successful_compiler(self):
        def run(*a,**k):
            assert self.source.parent == self.root
            self.source.unlink()
            return self.result()
        rec,_,_=g.compile_checked(["lean"],self.source,self.expected,{},runner=run)
        self.assertEqual(rec["exit_code"],125)
        self.assertIsNone(rec["source_sha256_after"])
    def test_compiler_failure_remains_failure(self):
        rec,_,_=g.compile_checked(["lean"],self.source,self.expected,{},runner=lambda *a,**k:self.result(7))
        self.assertEqual(rec["exit_code"],7)
        self.assertTrue(rec["source_hash_match"])
    def test_correct_environment_pins(self):
        rec=self.check_env()
        self.assertTrue(rec["passed"])
        self.assertEqual(rec["mathlib_git_head"],g.EXPECTED_MATHLIB_COMMIT)
        self.assertIn("lakefile.toml",rec["mathlib_source_pin_files"])
    def test_wrong_lean_rejected(self):
        with self.assertRaises(g.EnvironmentPinError) as e:self.check_env(version="4.32.0")
        self.assertEqual(e.exception.details["lean_version"],"4.32.0")
    def test_nightly_is_not_release_pin(self):
        with self.assertRaises(g.EnvironmentPinError):self.check_env(version="4.31.0-nightly")
    def test_wrong_mathlib_commit_rejected(self):
        with self.assertRaises(g.EnvironmentPinError) as e:self.check_env(head="0"*40)
        self.assertEqual(e.exception.details["mathlib_git_head"],"0"*40)
    def test_wrong_git_root_rejected(self):
        with self.assertRaises(g.EnvironmentPinError):self.check_env(root_override=self.root)
    def test_first_shadow_provider_is_not_skipped(self):
        shadow=self.root/"shadow"
        (shadow/"Mathlib").mkdir(parents=True)
        with self.assertRaises(g.EnvironmentPinError) as e:self.check_env(first_provider=shadow)
        self.assertEqual(e.exception.details["mathlib_lean_path_entry"],str(shadow.resolve()))
    def test_git_missing_rejected(self):
        with self.assertRaises(g.EnvironmentPinError):self.check_env(git_available=False)
    def test_no_mathlib_provider_rejected(self):
        with patch.object(g.subprocess,"check_output",return_value="Lean (version 4.31.0, platform)"):
            with self.assertRaises(g.EnvironmentPinError):g.verify_environment_pins("lean",{"LEAN_PATH":""})

if __name__=="__main__":unittest.main(verbosity=2)
