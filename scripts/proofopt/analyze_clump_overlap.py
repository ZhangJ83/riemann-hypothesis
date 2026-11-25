#!/usr/bin/env python3
"""Report import overlap between Lean modules, including modules packed by clump.py.

This is a source-level reconnaissance tool for ProofOpt. It deliberately does not
claim that shared imports imply shared proof terms: that requires Lean environment
inspection and kernel-checked experiments.

Usage:
  python3 scripts/proofopt/analyze_clump_overlap.py FILE_A.lean FILE_B.lean [...]
  python3 scripts/proofopt/analyze_clump_overlap.py --self-test
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from pathlib import Path

IMPORT_RE = re.compile(r"^(?:public\s+)?import\s+(.+?)\s*$")
MEMBER_RE = re.compile(r"^-- clump-header: (\{.*\})$")
CLUMP_MEMBER_RE = re.compile(r"^-- ===== clump member: (.+) =====$")
DECL_RE = re.compile(
    r"^(?:(?:private|protected|noncomputable|unsafe|public|nonrec|scoped|local)\s+)*"
    r"(?:theorem|lemma|def|abbrev|opaque|instance|structure|class|inductive)\s+([^\s:({\[]+)"
)


def imports_from_header(header: str) -> list[str]:
    found: list[str] = []
    for line in header.splitlines():
        match = IMPORT_RE.match(line.strip())
        if match:
            found.append(match.group(1))
    return found


def inspect_source(text: str) -> dict:
    """Extract the visible module imports and original imports embedded in clump seams."""
    lines = text.splitlines()
    module_header: list[str] = []
    for line in lines:
        stripped = line.strip()
        if stripped == "" or stripped.startswith("--"):
            module_header.append(line)
            continue
        if IMPORT_RE.match(stripped) or stripped == "module":
            module_header.append(line)
            continue
        break

    members: list[dict] = []
    current_name: str | None = None
    current_header: str | None = None
    for line in lines:
        member_match = CLUMP_MEMBER_RE.match(line)
        if member_match:
            current_name = member_match.group(1)
            current_header = None
            continue
        header_match = MEMBER_RE.match(line)
        if header_match and current_name:
            try:
                payload = json.loads(header_match.group(1))
                current_header = payload.get("h", "")
            except json.JSONDecodeError:
                current_header = ""
            members.append({
                "module": current_name,
                "imports": imports_from_header(current_header or ""),
            })
            current_name = None
            current_header = None

    visible_imports = imports_from_header("\n".join(module_header))
    # For clumped files, the outer header is the effective module interface. Member
    # headers preserve provenance and are reported separately, not added to effective
    # imports (which would double-count imports hidden by the clump transformation).
    return {
        "effective_imports": sorted(set(visible_imports)),
        "effective_import_count": len(set(visible_imports)),
        "clump_members": members,
        "clump_member_count": len(members),
        "source_lines": len(lines),
        "source_bytes": len(text.encode("utf-8")),
    }


def compare(paths: list[Path]) -> dict:
    records = []
    for path in paths:
        text = path.read_text(encoding="utf-8")
        records.append({"path": str(path), **inspect_source(text)})

    pairwise = []
    for i, left in enumerate(records):
        a = set(left["effective_imports"])
        for right in records[i + 1:]:
            b = set(right["effective_imports"])
            shared = sorted(a & b)
            union = a | b
            pairwise.append({
                "left": left["path"],
                "right": right["path"],
                "left_imports": len(a),
                "right_imports": len(b),
                "shared_imports": len(shared),
                "union_imports": len(union),
                "jaccard": (len(shared) / len(union)) if union else 1.0,
                "shared": shared,
            })
    return {
        "schema": 1,
        "warning": (
            "Import overlap is only a module-level proxy. It is not proof-term "
            "duplication, not a dependency-closure count, and not a measured optimization."
        ),
        "files": records,
        "pairwise": pairwise,
    }


def self_test() -> None:
    sample = """module

public import A.B
import C.D

-- This file was produced by scripts/clump.py
-- ===== clump member: X.Y =====
-- clump-header: {"m":"X.Y","h":"module\\n\\npublic import A.B\\nimport Z.Q\\n"}
section
theorem foo : True := by trivial
end -- clump:auto
-- ===== end clump member: X.Y =====
"""
    report = inspect_source(sample)
    assert report["effective_imports"] == ["A.B", "C.D"]
    assert report["clump_member_count"] == 1
    assert report["clump_members"][0]["module"] == "X.Y"
    assert report["clump_members"][0]["imports"] == ["A.B", "Z.Q"]
    print("self-test: PASS")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("files", nargs="*", type=Path)
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if len(args.files) < 2:
        parser.error("provide at least two Lean source files, or use --self-test")
    report = compare(args.files)
    rendered = json.dumps(report, indent=2, ensure_ascii=False) + "\n"
    if args.output:
        args.output.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
