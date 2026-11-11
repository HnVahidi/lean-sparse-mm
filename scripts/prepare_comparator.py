#!/usr/bin/env python3
"""Generate private kernel config and bind a local result to source/tool hashes."""

from datetime import datetime, timezone
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys

from source_snapshot import digest, write_json

ROOT = Path(__file__).resolve().parents[1]
TOOLS = ("lake", "lean", "leanexport", "leanchecker", "nanoda_bin", "con-ron")
ALLOWED = {"challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms", "enable_nanoda"}


def tool_hashes(prefix):
    tools = {name: prefix / "bin" / name for name in TOOLS}
    bwrap = shutil.which("bwrap")
    if bwrap is None:
        raise ValueError("Bubblewrap is required for Comparator")
    tools["bwrap"] = Path(bwrap)
    return {name: {"executable": path.name, "sha256": digest(path)} for name, path in tools.items()}


def main():
    if sys.argv[1] == "--record-exit":
        code, log_code = map(int, sys.argv[2:4])
        prefix, effective_path, report_path = map(Path, sys.argv[4:7])
        report = json.loads(report_path.read_text(encoding="utf-8"))
        for relative, expected in report["source_sha256"].items():
            if digest(ROOT / relative) != expected:
                raise ValueError(f"Source changed during verification: {relative}")
        if tool_hashes(prefix) != report["tools"]:
            raise ValueError("A verifier executable changed during verification")
        if digest(effective_path) != report["effective_config_sha256"]:
            raise ValueError("Effective Comparator configuration changed during verification")
        if digest(report_path.parent / "source-snapshot.json") != report["source_snapshot_sha256"]:
            raise ValueError("Source snapshot record changed during verification")
        log_path = report_path.parent / "comparator.log"
        log = log_path.read_text(encoding="utf-8") if log_path.exists() else ""
        markers = {"Lean": "Lean default kernel accepts the solution", "NanoDa": "nanoda kernel accepts the solution", "con-ron": "con-ron kernel accepts the solution"}
        accepted = [kernel for kernel, marker in markers.items() if marker in log.splitlines()]
        strict_passed = code == 0 and log_code == 0 and len(accepted) == len(markers) and "Your solution is okay!" in log.splitlines()
        report.update({"completed_at_utc": datetime.now(timezone.utc).isoformat(),
            "comparator_exit_code": code, "log_write_exit_code": log_code,
            "comparator_log_sha256": digest(log_path) if log_path.exists() else None,
            "strict_local_outcome": "passed" if strict_passed else "failed", "accepted_kernels": accepted,
            "kernel_acceptance_basis": "Explicit acceptance markers from the retained Comparator log."})
        write_json(report_path, report)
        if not strict_passed:
            raise ValueError("Comparator, evidence writing, or an independent kernel did not pass")
        return
    prefix, effective_path, report_path = map(Path, sys.argv[1:4])
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    if not isinstance(config, dict) or set(config) - ALLOWED:
        raise ValueError("Unsupported submitted Comparator configuration fields")
    if not set(config.get("permitted_axioms", [])) <= {"propext", "Quot.sound", "Classical.choice"}:
        raise ValueError("Unpermitted axiom configuration")
    expected = (ROOT / "lean-toolchain").read_text().strip().removeprefix("leanprover/lean4:v")
    actual = subprocess.check_output([str(prefix / "bin" / "lean"), "--version"], text=True).strip()
    if not re.search(r"\bversion " + re.escape(expected) + r"(?:,|\b)", actual):
        raise ValueError(f"Compiler version does not match pin {expected}: {actual}")
    bwrap_version = subprocess.check_output(["bwrap", "--version"], text=True).strip()
    version_match = re.search(r"(\d+)\.(\d+)\.(\d+)", bwrap_version)
    if not version_match or tuple(map(int, version_match.groups())) < (0, 12, 0):
        raise ValueError("Bubblewrap 0.12.0 or later is required for this verification workflow")
    config.pop("enable_nanoda", None)
    selected = {key: config[key] for key in ("theorem_names", "definition_names", "permitted_axioms")}
    config["external_kernels"] = {"nanoda": [str(prefix / "bin" / "nanoda_bin")], "con-ron": [str(prefix / "bin" / "con-ron")]}
    write_json(effective_path, config)
    snapshot_path = report_path.parent / "source-snapshot.json"
    snapshot = json.loads(snapshot_path.read_text(encoding="utf-8"))
    report = {"kind": "local Palomar-style verification", "started_at_utc": datetime.now(timezone.utc).isoformat(),
              "source_commit": snapshot["source_commit"], "source_snapshot_sha256": digest(snapshot_path),
              "source_sha256": {name: value["sha256"] for name, value in snapshot["files"].items()},
              "lean_version": actual, "bubblewrap_version": bwrap_version,
              "tools": tool_hashes(prefix), "comparator_config": "comparator.json",
              "comparator_config_sha256": digest(ROOT / "comparator.json"),
              "effective_config_sha256": digest(effective_path),
              "external_kernels": {"nanoda": "nanoda_bin", "con-ron": "con-ron"},
              **selected}
    write_json(report_path, report)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"Comparator preparation failed: {error}", file=sys.stderr)
        raise SystemExit(1)
