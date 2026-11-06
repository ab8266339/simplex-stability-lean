"""Standard-library guards for pinned dependencies and immutable Lean snapshots."""
import hashlib
import os
import pathlib
import re
import shutil
import subprocess

EXPECTED_LEAN_VERSION = "4.31.0"
EXPECTED_MATHLIB_COMMIT = "fabf563a7c95a166b8d7b6efca11c8b4dc9d911f"

class EnvironmentPinError(RuntimeError):
    def __init__(self, message, details):
        super().__init__(message)
        self.details = details

def source_sha256(path):
    return hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest()

def verify_environment_pins(lean, env):
    """Check the executable and first Mathlib provider on the actual LEAN_PATH."""
    details = {
        "expected_lean_version": EXPECTED_LEAN_VERSION,
        "expected_mathlib_commit": EXPECTED_MATHLIB_COMMIT,
        "passed": False,
    }
    def fail(message):
        raise EnvironmentPinError(message, details.copy())
    try:
        version = subprocess.check_output([lean, "--version"], env=env, text=True,
            encoding="utf-8", stderr=subprocess.STDOUT).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        fail("Cannot read Lean version: " + str(exc))
    details["lean_version_output"] = version
    match = re.search(r"\bversion\s+([^,\s)]+)", version)
    details["lean_version"] = match.group(1) if match else None
    if details["lean_version"] != EXPECTED_LEAN_VERSION:
        fail("Lean version mismatch: expected " + EXPECTED_LEAN_VERSION)

    provider = None
    for entry in env.get("LEAN_PATH", "").split(os.pathsep):
        if not entry:
            continue
        candidate = pathlib.Path(entry).resolve()
        if (candidate / "Mathlib").is_dir() or (candidate / "Mathlib.olean").is_file():
            provider = candidate
            break
    if provider is None:
        fail("No Mathlib provider found on the effective LEAN_PATH")
    details["mathlib_lean_path_entry"] = str(provider)
    # A compiled Mathlib directory alone is not a source repository. Require
    # the source aggregator and source tree when walking the provider's parents.
    source_root = next((p for p in (provider, *provider.parents)
        if (p / "Mathlib").is_dir() and (p / "Mathlib.lean").is_file()
        and ((p / "lakefile.lean").is_file() or (p / "lakefile.toml").is_file())), None)
    if source_root is None:
        fail("The first Mathlib provider has no discoverable Mathlib source root")
    details["mathlib_source_root"] = str(source_root)
    git = shutil.which("git", path=env.get("PATH"))
    if git is None:
        fail("git is required to validate the actual Mathlib source revision")
    try:
        git_root_text = subprocess.check_output(
            [git, "-C", str(source_root), "rev-parse", "--show-toplevel"],
            env=env, text=True, encoding="utf-8", stderr=subprocess.STDOUT).strip()
        head = subprocess.check_output(
            [git, "-C", str(source_root), "rev-parse", "HEAD"],
            env=env, text=True, encoding="utf-8", stderr=subprocess.STDOUT).strip()
    except (OSError, subprocess.CalledProcessError) as exc:
        fail("Cannot verify the Mathlib git repository: " + str(exc))
    details["mathlib_git_root"] = git_root_text
    details["mathlib_git_head"] = head
    if pathlib.Path(git_root_text).resolve() != source_root:
        fail("Discovered Mathlib source is not the root of its own git repository")
    if head.lower() != EXPECTED_MATHLIB_COMMIT:
        fail("Mathlib revision mismatch: expected " + EXPECTED_MATHLIB_COMMIT)
    details["mathlib_source_pin_files"] = {
        name: source_sha256(source_root / name)
        for name in ("lean-toolchain", "lakefile.lean", "lakefile.toml")
        if (source_root / name).is_file()
    }
    details["passed"] = True
    return details

def compile_checked(command, source, expected_sha256, env, runner=None):
    """Run only the visited snapshot; reject changes before or during compilation."""
    source = pathlib.Path(source)
    rec = {"command": command, "expected_source_sha256": expected_sha256,
        "source_sha256_before": None, "source_sha256_after": None,
        "source_sha256": None, "source_hash_match": False,
        "compiler_ran": False, "compiler_exit_code": None, "exit_code": 125}
    try:
        rec["source_sha256_before"] = source_sha256(source)
    except OSError as exc:
        rec["source_hash_error"] = "Snapshot unreadable before compile: " + str(exc)
        return rec, "", rec["source_hash_error"] + "\n"
    if rec["source_sha256_before"] != expected_sha256:
        rec["source_sha256_after"] = rec["source_sha256_before"]
        rec["source_sha256"] = rec["source_sha256_before"]
        rec["source_hash_error"] = "Snapshot hash differs from its creation hash before compile"
        return rec, "", rec["source_hash_error"] + "\n"
    runner = subprocess.run if runner is None else runner
    result = runner(command, env=env, capture_output=True, text=True,
        encoding="utf-8", errors="replace")
    rec["compiler_ran"] = True
    rec["compiler_exit_code"] = result.returncode
    try:
        rec["source_sha256_after"] = source_sha256(source)
        rec["source_sha256"] = rec["source_sha256_after"]
    except OSError as exc:
        rec["source_hash_error"] = "Snapshot unreadable after compile: " + str(exc)
    rec["source_hash_match"] = (
        rec["source_sha256_before"] == expected_sha256
        and rec["source_sha256_after"] == expected_sha256)
    if not rec["source_hash_match"]:
        rec.setdefault("source_hash_error", "Snapshot hash changed during compile")
    rec["exit_code"] = result.returncode if rec["source_hash_match"] else 125
    stderr = result.stderr + (
        "\n" + rec["source_hash_error"] + "\n" if "source_hash_error" in rec else "")
    return rec, result.stdout, stderr
