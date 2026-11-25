#!/usr/bin/env python3
"""Build a source-level import graph for a Lean project and its clumped modules.

This analyzer reconstructs the original module graph from scripts/clump.py seam
headers where available, maps original modules to their current physical file, and
computes dependency closures for explicitly supplied root modules.

It is intentionally conservative: it measures module imports, not Lean declaration
or proof-term dependencies. Use Lean environment/export data for those stronger claims.

Usage:
  python3 scripts/proofopt/global_import_graph.py --src src --roots Main --json report.json
  python3 scripts/proofopt/global_import_graph.py --self-test
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter, defaultdict, deque
from pathlib import Path
from typing import Iterable

IMPORT_RE = re.compile(r"^(?:public\\s+)?import\\s+(.+?)\\s*$")
MEMBER_RE = re.compile(r"^-- clump-header: (\\{.*\\})$")
CLUMP_MEMBER_RE = re.compile(r"^-- ===== clump member: (.+) =====$")


def module_name(path: Path, src_root: Path) -> str:
    return ".".join(path.relative_to(src_root).with_suffix("").parts)


def parse_imports(header: str) -> list[str]:
    result = []
    for line in header.splitlines():
        m = IMPORT_RE.match(line.strip())
        if m:
            result.append(m.group(1))
    return result


def parse_lean_file(text: str) -> dict:
    """Return effective imports and clump member provenance from one source file."""
    lines = text.splitlines()
    outer_header = []
    for line in lines:
        stripped = line.strip()
        if stripped == "" or stripped.startswith("--"):
            outer_header.append(line)
        elif stripped == "module" or IMPORT_RE.match(stripped):
            outer_header.append(line)
        else:
            break

    members = []
    current_member = None
    for line in lines:
        m = CLUMP_MEMBER_RE.match(line)
        if m:
            current_member = m.group(1)
            continue
        m = MEMBER_RE.match(line)
        if m and current_member:
            try:
                header = json.loads(m.group(1)).get("h", "")
            except (json.JSONDecodeError, AttributeError):
                header = ""
            members.append({
                "module": current_member,
                "imports": sorted(set(parse_imports(header))),
            })
            current_member = None

    return {
        "imports": sorted(set(parse_imports("\\n".join(outer_header)))),
        "members": members,
        "is_clump": bool(members),
    }


class ImportGraph:
    def __init__(self) -> None:
        self.edges: dict[str, set[str]] = defaultdict(set)
        self.physical: dict[str, str] = {}
        self.external: Counter[str] = Counter()
        self.clumps: dict[str, list[str]] = {}

    def add_file(self, physical_module: str, physical_path: str, parsed: dict) -> None:
        if parsed["is_clump"]:
            members = parsed["members"]
            names = [m["module"] for m in members]
            self.clumps[physical_module] = names
            for member in members:
                name = member["module"]
                self.physical[name] = physical_path
                self.edges[name].update(member["imports"])
            # The physical root's outer imports are the effective dependency
            # interface. Preserve them as the root member's outgoing edges.
            if physical_module in self.edges:
                self.edges[physical_module].update(parsed["imports"])
            else:
                self.edges[physical_module].update(parsed["imports"])
        else:
            self.physical[physical_module] = physical_path
            self.edges[physical_module].update(parsed["imports"])

    def finalize(self) -> None:
        known = set(self.edges)
        for source, targets in self.edges.items():
            for target in targets:
                if target not in known:
                    self.external[target] += 1

    def closure(self, roots: Iterable[str]) -> set[str]:
        seen: set[str] = set()
        todo = list(roots)
        while todo:
            node = todo.pop()
            if node in seen:
                continue
            seen.add(node)
            todo.extend(self.edges.get(node, ()))
        return seen

    def internal_closure(self, roots: Iterable[str]) -> set[str]:
        known = set(self.edges)
        return self.closure(roots) & known

    def shared_dependency_report(self, roots: list[str]) -> list[dict]:
        per_root = {root: self.internal_closure([root]) for root in roots}
        counts = Counter(node for closure in per_root.values() for node in closure)
        result = []
        for node, count in counts.most_common():
            if count > 1:
                result.append({
                    "module": node,
                    "root_count": count,
                    "roots": [r for r, closure in per_root.items() if node in closure],
                    "physical_file": self.physical.get(node),
                    "direct_import_count": len(self.edges.get(node, ())),
                })
        return result

    def cycles(self) -> list[list[str]]:
        """Find strongly connected components using Tarjan's algorithm."""
        index = 0
        stack: list[str] = []
        on_stack: set[str] = set()
        indices: dict[str, int] = {}
        low: dict[str, int] = {}
        components: list[list[str]] = []

        def visit(v: str) -> None:
            nonlocal index
            indices[v] = low[v] = index
            index += 1
            stack.append(v)
            on_stack.add(v)
            for w in self.edges.get(v, ()):
                if w not in self.edges:
                    continue
                if w not in indices:
                    visit(w)
                    low[v] = min(low[v], low[w])
                elif w in on_stack:
                    low[v] = min(low[v], indices[w])
            if low[v] == indices[v]:
                component = []
                while True:
                    w = stack.pop()
                    on_stack.remove(w)
                    component.append(w)
                    if w == v:
                        break
                if len(component) > 1 or v in self.edges.get(v, ()):
                    components.append(sorted(component))

        for node in self.edges:
            if node not in indices:
                visit(node)
        return sorted(components)


def build_graph(src_root: Path) -> ImportGraph:
    graph = ImportGraph()
    for path in sorted(src_root.rglob("*.lean")):
        physical = module_name(path, src_root)
        parsed = parse_lean_file(path.read_text(encoding="utf-8"))
        graph.add_file(physical, str(path), parsed)
    graph.finalize()
    return graph


def make_report(graph: ImportGraph, roots: list[str]) -> dict:
    known = set(graph.edges)
    missing_roots = [root for root in roots if root not in known]
    closures = {root: graph.internal_closure([root]) for root in roots if root in known}
    union = set().union(*closures.values()) if closures else set()
    return {
        "schema": 1,
        "measurement": "source-level module import graph",
        "warning": (
            "This is not a declaration-level Lean dependency closure and not a proof-term DAG. "
            "Clump member headers are provenance metadata; their source-level edges are approximate."
        ),
        "roots": roots,
        "missing_roots": missing_roots,
        "module_count": len(known),
        "edge_count": sum(len(v) for v in graph.edges.values()),
        "external_import_count": sum(graph.external.values()),
        "external_imports": graph.external.most_common(100),
        "clump_count": len(graph.clumps),
        "clump_member_count": sum(map(len, graph.clumps.values())),
        "root_closures": {
            root: {
                "internal_module_count": len(closure),
                "modules": sorted(closure),
            } for root, closure in closures.items()
        },
        "union_closure_count": len(union),
        "shared_dependencies": graph.shared_dependency_report(list(closures)),
        "cycles": graph.cycles(),
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
    parsed = parse_lean_file(sample)
    assert parsed["imports"] == ["A.B", "C.D"]
    assert parsed["is_clump"]
    assert parsed["members"] == [{"module": "X.Y", "imports": ["A.B", "Z.Q"]}]

    g = ImportGraph()
    g.add_file("RootA", "RootA.lean", {"imports": ["Shared", "OnlyA"], "members": [], "is_clump": False})
    g.add_file("RootB", "RootB.lean", {"imports": ["Shared", "OnlyB"], "members": [], "is_clump": False})
    g.add_file("Shared", "Shared.lean", {"imports": [], "members": [], "is_clump": False})
    g.add_file("OnlyA", "OnlyA.lean", {"imports": [], "members": [], "is_clump": False})
    g.add_file("OnlyB", "OnlyB.lean", {"imports": [], "members": [], "is_clump": False})
    g.finalize()
    assert g.internal_closure(["RootA"]) == {"RootA", "Shared", "OnlyA"}
    assert g.internal_closure(["RootB"]) == {"RootB", "Shared", "OnlyB"}
    shared = g.shared_dependency_report(["RootA", "RootB"])
    assert shared[0]["module"] == "Shared" and shared[0]["root_count"] == 2
    assert make_report(g, ["RootA", "RootB"])["union_closure_count"] == 5

    cyc = ImportGraph()
    cyc.add_file("A", "A.lean", {"imports": ["B"], "members": [], "is_clump": False})
    cyc.add_file("B", "B.lean", {"imports": ["A"], "members": [], "is_clump": False})
    assert cyc.cycles() == [["A", "B"]]
    print("self-test: PASS (clump parsing, closure, shared dependencies, union, cycle detection)")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--src", type=Path, default=Path("src"))
    parser.add_argument("--roots", nargs="+", default=["Main"])
    parser.add_argument("--json", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return 0
    if not args.src.is_dir():
        parser.error(f"source directory does not exist: {args.src}")
    graph = build_graph(args.src)
    report = make_report(graph, args.roots)
    rendered = json.dumps(report, indent=2, ensure_ascii=False) + "\\n"
    if args.json:
        args.json.write_text(rendered, encoding="utf-8")
    else:
        sys.stdout.write(rendered)
    print(
        f"modules={report['module_count']} edges={report['edge_count']} "
        f"closure={report['union_closure_count']} clumps={report['clump_count']} "
        f"cycles={len(report['cycles'])}",
        file=sys.stderr,
    )
    return 1 if report["missing_roots"] or report["cycles"] else 0


if __name__ == "__main__":
    raise SystemExit(main())
