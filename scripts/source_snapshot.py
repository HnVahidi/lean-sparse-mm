#!/usr/bin/env python3
"""Materialize and verify the regular files at one local Git commit."""

import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess


GENERATED = {".git", ".lake", "__pycache__"}
COMPILED = {".olean", ".ilean", ".a", ".bc", ".dll", ".dylib", ".o", ".obj", ".so", ".trace"}


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + "\n", encoding="utf-8")


def git(repo, *arguments):
    return subprocess.check_output(["git", "-C", str(repo), *arguments])


def create(repo, commit, destination, report):
    if not re.fullmatch(r"[0-9a-f]{40}", commit):
        raise ValueError("Expected a full 40-character source commit")
    if any(destination.iterdir()):
        raise ValueError("Snapshot destination must be empty")
    entries = git(repo, "ls-tree", "-r", "-z", "--full-tree", commit).split(b"\0")
    files = {}
    for entry in filter(None, entries):
        header, raw_path = entry.split(b"\t", 1)
        mode, kind, oid = header.decode("ascii").split()
        relative = PurePosixPath(raw_path.decode("utf-8"))
        if relative.is_absolute() or ".." in relative.parts or GENERATED.intersection(relative.parts):
            raise ValueError(f"Unsupported tracked path {relative}")
        if kind != "blob" or mode not in {"100644", "100755"}:
            raise ValueError(f"Expected a regular file at {relative}")
        if relative.suffix in COMPILED or relative.name == ".gitmodules":
            raise ValueError(f"Unexpected build output or submodule configuration at {relative}")
        data = git(repo, "cat-file", "blob", oid)
        if data.startswith(b"version https://git-lfs.github.com/spec/v1"):
            raise ValueError(f"Git LFS pointer at {relative}")
        target = destination / relative
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
        target.chmod(int(mode, 8) & 0o777)
        files[str(relative)] = {"git_blob": oid, "sha256": hashlib.sha256(data).hexdigest(), "mode": mode}
    write_json(report, {"source_commit": commit, "files": files})
    print(f"Materialized {len(files)} regular files from Git commit {commit}.")


def verify(root, manifest, report, exact):
    snapshot = json.loads(manifest.read_text(encoding="utf-8"))
    files = snapshot["files"]
    changed = []
    for relative, record in files.items():
        path = root / relative
        if path.is_symlink() or not path.is_file() or digest(path) != record["sha256"]:
            changed.append(relative)
    additional = []
    if exact:
        for directory, subdirs, names in os.walk(root):
            subdirs[:] = [name for name in subdirs if name not in GENERATED]
            for name in names:
                relative = (Path(directory) / name).relative_to(root).as_posix()
                if relative not in files:
                    additional.append(relative)
    passed = bool(files) and not changed and not additional
    write_json(report, {"source_commit": snapshot["source_commit"], "passed": passed,
                        "file_count": len(files), "changed": changed, "additional": sorted(additional)})
    print(f"Source byte comparison for {len(files)} files: {'passed' if passed else 'FAILED'}.")
    return int(not passed)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    create_parser = commands.add_parser("create")
    create_parser.add_argument("repo", type=Path)
    create_parser.add_argument("commit")
    create_parser.add_argument("destination", type=Path)
    create_parser.add_argument("report", type=Path)
    verify_parser = commands.add_parser("verify")
    verify_parser.add_argument("root", type=Path)
    verify_parser.add_argument("manifest", type=Path)
    verify_parser.add_argument("report", type=Path)
    verify_parser.add_argument("--exact", action="store_true")
    args = parser.parse_args()
    if args.command == "create":
        create(args.repo, args.commit, args.destination, args.report)
        return 0
    return verify(args.root, args.manifest, args.report, args.exact)


if __name__ == "__main__":
    raise SystemExit(main())
