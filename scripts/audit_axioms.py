#!/usr/bin/env python3
"""Audit each selected declaration in the compiled Solution."""

from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_']*(?:\.[A-Za-z_][A-Za-z0-9_']*)*\Z")
STANDARD = {"propext", "Quot.sound", "Classical.choice"}


def main():
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    module = config["solution_module"]
    names = config["theorem_names"] + config.get("definition_names", [])
    allowed = set(config["permitted_axioms"])
    if not names or len(names) != len(set(names)) or not all(isinstance(s, str) and NAME.fullmatch(s) for s in [module] + names):
        raise ValueError("Invalid or empty declaration/module list")
    if not allowed <= STANDARD:
        raise ValueError("Only Lean's three standard axioms may be permitted")
    output = ROOT / ".lake" / "verification"
    output.mkdir(parents=True, exist_ok=True)
    evidence = Path(sys.argv[1]) if len(sys.argv) == 2 else output
    query = output / "Axioms.lean"
    query.write_text("module\nimport " + module + "\n\n" + "\n".join("#print axioms " + n for n in names) + "\n", encoding="utf-8")
    result = subprocess.run(["lake", "env", "lean", str(query)], cwd=ROOT, text=True, capture_output=True)
    log = result.stdout + result.stderr
    (evidence / "axioms.log").write_text(log, encoding="utf-8")
    print(log, end="")
    if result.returncode:
        return result.returncode
    found = {}
    for name, axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", log):
        found[name] = [s.strip() for s in axioms.split(",") if s.strip()]
    for name in re.findall(r"'([^']+)' does not depend on any axioms", log):
        found[name] = []
    if set(found) != set(names):
        raise ValueError(f"Axiom output incomplete: expected {names}, found {list(found)}")
    prohibited = {name: sorted(set(values) - allowed) for name, values in found.items() if not set(values) <= allowed}
    report = {"generated_at_utc": datetime.now(timezone.utc).isoformat(), "declarations": {name: found[name] for name in names}, "permitted_axioms": sorted(allowed), "passed": not prohibited, "prohibited": prohibited}
    (evidence / "axioms.json").write_text(json.dumps(report, indent=2) + "\n", encoding="utf-8")
    if prohibited:
        raise ValueError(f"Unpermitted axioms: {prohibited}")
    return 0


if __name__ == "__main__":
    try:
        raise SystemExit(main())
    except (OSError, ValueError, KeyError, subprocess.CalledProcessError) as error:
        print(f"Axiom audit failed: {error}", file=sys.stderr)
        raise SystemExit(1)
