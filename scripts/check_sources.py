#!/usr/bin/env python3
"""Check the small project's source discipline; the kernels check proof terms."""

import json
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[1]
IMPORT = re.compile(r"^\s*(?:public\s+)?(?:meta\s+)?import\s+([A-Za-z_][A-Za-z0-9_.']*)", re.M)


def lean_files():
    for directory, subdirs, names in os.walk(ROOT):
        subdirs[:] = [name for name in subdirs if name not in {".git", ".lake", "__pycache__"}]
        yield from (Path(directory) / name for name in names if name.endswith(".lean"))


def without_comments(text):
    """Remove nested Lean comments and strings, preserving newline positions."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if depth:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if text[i] == "\n" else " ")
                i += 1
        elif text.startswith("/-", i):
            depth = 1
            i += 2
        elif text.startswith("--", i):
            j = text.find("\n", i)
            i = len(text) if j < 0 else j
        elif text[i] == '"':
            out.append(" ")
            i += 1
            while i < len(text):
                if text[i] == "\\":
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    out.append("\n" if text[i] == "\n" else " ")
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError("Unclosed block comment")
    return "".join(out)


def main():
    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    errors, files, holes, imports = [], [], 0, set()
    for path in sorted(lean_files()):
        rel = path.relative_to(ROOT)
        if path.is_symlink():
            errors.append(f"{rel}: symbolic link")
            continue
        files.append(rel.as_posix())
        data = path.read_bytes()
        source = data.decode("utf-8-sig")
        code = without_comments(source)
        direct_imports = set(IMPORT.findall(code))
        imports.update(name for name in direct_imports if name.split(".", 1)[0] == "Mathlib")
        lines = source.count("\n") + int(bool(source) and not source.endswith("\n"))
        if path.name != "lakefile.lean" and not re.match(r"\s*module\b", code):
            errors.append(f"{rel}: missing module header")
        if lines > 10000:
            errors.append(f"{rel}: source exceeds 10000 physical lines")
        if rel.as_posix() == "Challenge.lean":
            holes = len(re.findall(r"\bsorry\b", code))
            if len(data) > 102400 or lines > 1000:
                errors.append("Challenge.lean exceeds Palomar's hard size limit")
            if holes != len(config["theorem_names"]):
                errors.append("Challenge must contain one statement placeholder per selected theorem")
            for mod in sorted(direct_imports):
                if mod.split(".", 1)[0] not in {"Mathlib", "Init", "Lean", "Std"}:
                    errors.append(f"Challenge imports project-specific/unapproved module {mod}")
        else:
            if "Challenge" in direct_imports:
                errors.append(f"{rel}: imports Challenge")
            for token in ("sorry", "admit", "axiom", "native_decide", "unsafe", "implemented_by", "extern"):
                if re.search(rf"\b{token}\b", code):
                    errors.append(f"{rel}: forbidden proof-development token {token}")
    if not {"Challenge.lean", "Solution.lean", "SparseMM.lean"}.issubset(files):
        errors.append("Missing the Challenge, Solution or SparseMM root module")
    for error in errors:
        print(error, file=sys.stderr)
    if errors:
        return 1
    if sys.argv[1:] == ["--mathlib-imports"]:
        print("\n".join(sorted(imports)))
    elif not sys.argv[1:]:
        print(f"Source discipline passed for {len(files)} files with {holes} deliberate Challenge statement holes.")
    else:
        raise SystemExit("Usage: check_sources.py [--mathlib-imports]")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
