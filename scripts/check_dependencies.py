#!/usr/bin/env python3
"""Verify local dependency source copies match the committed Git manifest."""

import json
from pathlib import Path
import re
import subprocess
import sys

from source_snapshot import digest, write_json

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest_path = ROOT / "lake-manifest.json"
    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
    if manifest["packagesDir"] != ".lake/packages":
        raise ValueError("Expected a contained .lake/packages directory")
    packages = manifest["packages"]
    names = [item["name"] for item in packages]
    if not packages or len(names) != len(set(names)) or "mathlib" not in names:
        raise ValueError("Expected a unique set of Git dependencies including Mathlib")
    for item in packages:
        if (item["type"] != "git" or item.get("subDir") is not None
            or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", item["name"])
            or not re.fullmatch(r"https://github\.com/[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", item["url"])
            or not re.fullmatch(r"[0-9a-f]{40}", item["rev"])):
            raise ValueError(f"Invalid public Git dependency pin for {item['name']}")
    mathlib = next(item for item in packages if item["name"] == "mathlib")
    if mathlib["url"].removesuffix(".git") != "https://github.com/leanprover-community/mathlib4":
        raise ValueError("Mathlib must come from its canonical repository")
    if sys.argv[1:] == ["--manifest-only"]:
        print(f"Manifest contains {len(packages)} fully pinned public Git dependencies.")
        return 0
    directory_out = Path(sys.argv[1]) if len(sys.argv) == 2 else ROOT / ".lake/verification"
    directory_out.mkdir(parents=True, exist_ok=True)
    rows = []
    for item in packages:
        directory = ROOT / manifest["packagesDir"] / item["name"]
        if directory.is_symlink() or not directory.is_dir():
            raise ValueError(f"Missing physical Git checkout for {item['name']}")
        revision = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True)
        origin = subprocess.check_output(["git", "-C", str(directory), "config", "--get", "remote.origin.url"], text=True).strip()
        rows.append({"name": item["name"], "url": item["url"], "expected_revision": item["rev"],
                     "actual_revision": revision, "tracked_source_clean": not dirty,
                     "origin_matches_manifest": origin.removesuffix(".git") == item["url"].removesuffix(".git")})
    mathlib_root = ROOT / ".lake/packages/mathlib"
    toolchain = (ROOT / "lean-toolchain").read_text().strip()
    mathlib_toolchain = (mathlib_root / "lean-toolchain").read_text().strip()
    inherited = json.loads((mathlib_root / "lake-manifest.json").read_text(encoding="utf-8"))["packages"]
    identities = lambda items: {(item["name"], item["url"].removesuffix(".git"), item["rev"]) for item in items}
    inherited_match = identities(inherited) == identities(item for item in packages if item["name"] != "mathlib")
    passed = toolchain == mathlib_toolchain and inherited_match and all(
        r["expected_revision"] == r["actual_revision"] and r["tracked_source_clean"] and r["origin_matches_manifest"]
        for r in rows)
    write_json(directory_out / "dependencies.json", {"passed": passed, "dependencies": rows,
        "manifest_sha256": digest(manifest_path), "toolchain": toolchain,
        "mathlib_toolchain": mathlib_toolchain, "mathlib_inherited_pins_match": inherited_match})
    print(f"Dependency source audit: {len(rows)} pinned packages; {'passed' if passed else 'FAILED'}.")
    return 0 if passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
