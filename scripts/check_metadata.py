#!/usr/bin/env python3
"""Validate pinned metadata schemas and the recorded paper/proof provenance."""

import json
import re
from pathlib import Path
import sys
import urllib.request

import jsonschema
import yaml

from source_snapshot import digest, write_json
import hashlib

ROOT = Path(__file__).resolve().parents[1]
SCHEMAS = {
    "formalization.yaml": (
        "https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/99c678e569c7c4c0772db297c5ddd5e4c9b6322e/schema/v0.4.schema.json",
        "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce",
    ),
    "CITATION.cff": (
        "https://raw.githubusercontent.com/citation-file-format/citation-file-format/396f738fb025b1d8acdb02a56ffc923f95dc8999/schema.json",
        "0b8d22140da702d766df318dcff3a91af2f39521298dcf36d76315fd99cc169b",
    ),
}


class UniqueKeyLoader(yaml.SafeLoader):
    """Reject duplicate keys and YAML merge keys in either document."""

    def construct_mapping(self, node, deep=False):
        mapping = {}
        for key_node, value_node in node.value:
            key = self.construct_object(key_node, deep=deep)
            if key in mapping:
                raise ValueError(f"Duplicate YAML key {key!r}")
            mapping[key] = self.construct_object(value_node, deep=deep)
        return mapping


def check_schema(name, url, expected):
    with urllib.request.urlopen(url, timeout=30) as response:
        raw = response.read()
    actual = hashlib.sha256(raw).hexdigest()
    if actual != expected:
        raise ValueError(f"Unexpected checksum for {name} schema")
    path = ROOT / name
    data = yaml.load(path.read_text(encoding="utf-8"), Loader=UniqueKeyLoader)
    validator = jsonschema.Draft7Validator(json.loads(raw), format_checker=jsonschema.FormatChecker())
    errors = [{"path": list(error.absolute_path), "message": error.message}
              for error in validator.iter_errors(data)]
    return data, {"schema_url": url, "schema_sha256": actual, "file_sha256": digest(path),
                  "passed": not errors, "errors": errors}


def check_provenance(metadata):
    path = ROOT / "docs/source-provenance.json"
    provenance = json.loads(path.read_text(encoding="utf-8"))
    manuscript = provenance["manuscript"]
    paper_files = {f"paper/{name}": sha for name, sha in manuscript["files"].items()}
    proof_files = provenance["formalization"]["original_proof_files_sha256"]
    expected = {**paper_files, **proof_files}
    actual = {path.relative_to(ROOT).as_posix() for path in (ROOT / "paper").iterdir()
              if path.suffix in {".tex", ".bib", ".pdf"}}
    actual_proofs = {path.relative_to(ROOT).as_posix() for path in (ROOT / "SparseMM").rglob("*.lean")}
    errors = []
    if actual != set(paper_files) or actual_proofs != set(proof_files):
        errors.append("Manuscript or proof file list differs from the recorded provenance")
    mismatched = [name for name, sha in expected.items()
                  if name not in actual | actual_proofs or digest(ROOT / name) != sha]
    if mismatched:
        errors.append(f"Unexpected manuscript/proof SHA-256 in {', '.join(mismatched)}")
    pdf_sha = manuscript["pdf_sha256"]
    if pdf_sha != paper_files.get("paper/sparse-mm.pdf"):
        errors.append("Inconsistent PDF SHA-256 in the provenance record")
    if pdf_sha not in (ROOT / "Challenge.lean").read_text(encoding="utf-8"):
        errors.append("Challenge does not identify the recorded PDF")
    if not any(source.get("id") == f"sha256:{pdf_sha}" for source in metadata["sources"]):
        errors.append("formalization.yaml does not identify the recorded PDF")
    attribution = {}
    for name in ("LICENSE", "paper/LICENSE", "NOTICE.md", "LICENSE_STATUS.md", "docs/licenses/Apache-2.0.txt"):
        file = ROOT / name
        if not file.is_file() or not file.stat().st_size:
            errors.append(f"Missing or empty attribution file {name}")
        else:
            attribution[name] = digest(file)
    return {"passed": not errors, "provenance_sha256": digest(path), "paper_pdf_sha256": pdf_sha,
            "checked_manuscript_files": len(paper_files), "checked_proof_files": len(proof_files),
            "attribution_sha256": attribution, "errors": errors}


def check_licensing_and_credit(metadata, citation):
    """Check the selected code licence, manuscript exclusion and author alignment."""
    errors = []
    expected_apache = "c71d239df91726fc519c6eb72d318ec65820627232b2f796219e87dcf35d0ab4"
    for name in ("LICENSE", "docs/licenses/Apache-2.0.txt"):
        path = ROOT / name
        if not path.is_file() or digest(path) != expected_apache:
            errors.append(f"{name} does not match the retained standard Apache-2.0 text")
    root_licences = [path.name for path in ROOT.iterdir() if path.is_file() and
                    re.fullmatch(r"(?:LICENSE|LICENCE|COPYING|UNLICENSE|OFL)(?:\.(?:md|markdown|txt))?",
                                 path.name, flags=re.IGNORECASE)]
    if root_licences != ["LICENSE"]:
        errors.append("Expected LICENSE as the sole conventional root licence file")
    if metadata["project"].get("license") != "Apache-2.0" or citation.get("license") != "Apache-2.0":
        errors.append("Formalization and citation code licences must both be Apache-2.0")
    licensing = metadata.get("licensing", {})
    code, paper = licensing.get("code", {}), licensing.get("paper", {})
    if (code.get("license"), code.get("license_file"), code.get("excluded_paths")) != (
            "Apache-2.0", "LICENSE", ["paper/**"]):
        errors.append("Code licence scope must explicitly exclude paper/**")
    if (paper.get("path"), paper.get("rights"), paper.get("notice_file")) != (
            "paper/", "All rights reserved", "paper/LICENSE"):
        errors.append("The manuscript must retain its separate paper/LICENSE rights notice")
    notice = ROOT / "paper/LICENSE"
    if not notice.is_file() or not notice.stat().st_size:
        errors.append("Missing manuscript rights notice")
    def names(entries):
        return [entry.get("name") or " ".join(
            filter(None, (entry.get("given-names"), entry.get("family-names")))) for entry in entries]
    authors = metadata["project"]["authors"]
    if names(citation.get("authors", [])) != authors:
        errors.append("CITATION.cff and formalization.yaml formalization authors differ")
    source = metadata["sources"][0]
    references = [reference for reference in citation.get("references", [])
                  if reference.get("title") == source["title"]]
    if len(references) != 1 or names(references[0].get("authors", [])) != source["authors"]:
        errors.append("The manuscript authors differ between citation and source metadata")
    return {"passed": not errors, "code_license": "Apache-2.0", "excluded_paths": ["paper/**"],
            "paper_rights": paper.get("rights"), "formalization_authors": authors,
            "responsible_maintainers": metadata["project"]["responsible_maintainers"], "errors": errors}


def main():
    directory = Path(sys.argv[1]) if len(sys.argv) == 2 else ROOT / ".lake/verification"
    directory.mkdir(parents=True, exist_ok=True)
    documents, schemas = {}, {}
    for name, (url, expected) in SCHEMAS.items():
        documents[name], schemas[name] = check_schema(name, url, expected)
        print(f"{name} schema validation {'passed' if schemas[name]['passed'] else 'FAILED'}.")
        for error in schemas[name]["errors"]:
            print(f"{name} {error['path']}: {error['message']}")
    schema_ok = all(item["passed"] for item in schemas.values())
    provenance = check_provenance(documents["formalization.yaml"]) if schema_ok else {"passed": False, "errors": []}
    for error in provenance["errors"]:
        print(error)
    print(f"Paper, proof and attribution provenance check {'passed' if provenance['passed'] else 'FAILED'}.")
    licensing = check_licensing_and_credit(documents["formalization.yaml"], documents["CITATION.cff"]) if schema_ok else {"passed": False, "errors": []}
    for error in licensing["errors"]:
        print(error)
    print(f"Code licence, manuscript exclusion and author consistency check {'passed' if licensing['passed'] else 'FAILED'}.")
    passed = schema_ok and provenance["passed"] and licensing["passed"]
    write_json(directory / "metadata.json", {"passed": passed, "schemas": schemas, "provenance": provenance,
                                             "licensing_and_credit": licensing, "registry_submission_ready": False})
    return int(not passed)


if __name__ == "__main__":
    raise SystemExit(main())
