#!/usr/bin/env python3
"""Census exact Lean declaration-reference twins across project modules.

A twin means equal sets of referenced names in type, kernel metadata and value.
It is only a candidate signal, NOT proof that types are definitionally equal or
that proof expressions/DAGs are equal. No declaration is rewritten or deleted.
"""
import argparse, gzip, hashlib, json, sys, unittest, tempfile
from collections import defaultdict, Counter
from pathlib import Path

GENERATED = ("_simp", "_private.", "._auxLemma", "._elabRules", "._eq_",
             "._match_", "._proof_", "._unary_", "._closed_", "._hyg.",
             ".eq_1", ".eq_def", ".eq_unfold", "._abel_", ".match_",
             ".proof_", ".recOn_", ".casesOn_")
GRAPH_SHA = "5a1f971e33e3c0449137327e7ed46ae4d8742c31e4c0e8449525005d03c5591c"
LINE_BUDGET = {
    "target": 2000,
    "unit": "nonblank, noncomment Lean source lines",
    "scope": "all project-owned Lean files containing at least one declaration reachable from the five final roots",
    "external": "Mathlib and TauCeti excluded from project LOC but separately pinned and reported; moving project proof obligations to a new package is forbidden",
    "status": "not measured by the reference graph; requires module reachability plus source-span mapping"
}
REAL_RUN = {
    "run_id": 45755058155, "artifact_id": 15087791705,
    "head_sha": "61730f76ac4dfbe7c7ae1ca0d96db546008ef099",
    "graph_sha256": GRAPH_SHA, "declarations": 887134,
    "project_theorems": 52065, "exact_twin_groups_all": 2175,
    "exact_twin_members_all": 16636,
    "exact_twin_groups_excluding_generated": 43,
    "exact_twin_members_excluding_generated": 88,
    "cross_module_groups_excluding_generated": 3,
    "cross_module_members_excluding_generated": 6,
    "analysis_wall_seconds": 12.62, "peak_rss_mib": 541.2
}

def generated(name):
    return any(x in name for x in GENERATED)

def signature(row):
    typ = tuple(sorted(set(row.get("type", []))))
    ker = tuple(sorted(set(row.get("kernel", []))))
    val = tuple(sorted(set(row.get("value", [])) - set(typ) - set(ker)))
    return typ, ker, val

def census(graph_path, modules_path, expected_sha=GRAPH_SHA):
    modules = set(Path(modules_path).read_text(encoding="utf-8").splitlines())
    digest, groups, names = hashlib.sha256(), defaultdict(list), set()
    declarations = project_theorems = 0
    with gzip.open(graph_path, "rb") as f:
        first = f.readline()
        if not first: raise ValueError("empty graph")
        digest.update(first); header = json.loads(first)
        if (header.get("schema"), header.get("record"), header.get("measurement")) != (1, "header", "kernel-reference-graph"):
            raise ValueError("unsupported graph header")
        for line_no, line in enumerate(f, 2):
            digest.update(line); row = json.loads(line)
            if row.get("record") != "decl": raise ValueError(f"invalid record at line {line_no}")
            name, module = row["name"], row["module"]
            if name in names: raise ValueError(f"duplicate declaration: {name}")
            names.add(name); declarations += 1
            if not row.get("project") or row.get("kind") != "thm": continue
            if module not in modules: raise ValueError(f"ownership mismatch: {name}")
            project_theorems += 1
            groups[signature(row)].append((name, module))
    actual = digest.hexdigest()
    if actual != expected_sha: raise ValueError(f"digest mismatch: {actual}")
    exact = [v for v in groups.values() if len(v) > 1]
    authored = [[x for x in v if not generated(x[0])] for v in exact]
    authored = [v for v in authored if len(v) > 1]
    cross = [v for v in authored if len({m for _, m in v}) > 1]
    cross.sort(key=lambda v: (-len(v), -len({m for _, m in v}), tuple(n for n, _ in v)))
    candidates = [{"members":[{"name":n,"module":m} for n,m in sorted(v)],
                   "member_count":len(v), "module_count":len({m for _,m in v}),
                   "status":"reference-signature twin; exact Lean Expr/type comparison required"}
                  for v in cross]
    return {
        "schema":1, "measurement":"exact-reference-signature-twin-census",
        "input_sha256":actual, "declarations":declarations,
        "project_theorems":project_theorems,
        "exact_twin_groups_all":len(exact),
        "exact_twin_members_all":sum(map(len,exact)),
        "exact_twin_groups_excluding_generated":len(authored),
        "exact_twin_members_excluding_generated":sum(map(len,authored)),
        "cross_module_groups_excluding_generated":len(cross),
        "cross_module_members_excluding_generated":sum(map(len,cross)),
        "cross_module_module_span_histogram":dict(sorted(Counter(len({m for _,m in v}) for v in cross).items())),
        "line_budget":LINE_BUDGET, "reference_run":REAL_RUN,
        "candidates":candidates,
        "limitations":[
            "Identical reference-name sets do not imply definitionally equal types.",
            "Identical reference-name sets do not imply equal proof expressions or proof DAGs.",
            "The graph omits expression structure and may omit implicit kernel dependencies.",
            "Generated-name filtering is heuristic, not semantic.",
            "No declaration is rewritten or deleted by this census."
        ]
    }

class Tests(unittest.TestCase):
    def row(self,n,m,typ=None,ker=None,val=None):
        return {"record":"decl","name":n,"module":m,"kind":"thm","project":True,
                "type":typ or ["Nat"],"kernel":ker or [],"value":val or ["Nat.add"]}
    def fixture(self, rows, modules="A\nB\n"):
        td=tempfile.TemporaryDirectory(); self.addCleanup(td.cleanup)
        root=Path(td.name); raw=root/"raw"; gz=root/"graph.gz"; mod=root/"modules"
        with raw.open("wb") as f:
            f.write((json.dumps({"schema":1,"record":"header","measurement":"kernel-reference-graph"})+"\n").encode())
            for r in rows: f.write((json.dumps(r,sort_keys=True)+"\n").encode())
        sha=hashlib.sha256(raw.read_bytes()).hexdigest()
        with raw.open("rb") as a,gzip.open(gz,"wb") as b: b.write(a.read())
        mod.write_text(modules); return gz,mod,sha
    def test_cross_module_twins(self):
        g,m,s=self.fixture([self.row("A.a","A"),self.row("B.b","B")])
        self.assertEqual(census(g,m,s)["cross_module_groups_excluding_generated"],1)
    def test_generated_filter(self):
        g,m,s=self.fixture([self.row("A.a","A"),self.row("B.a_simp","B")])
        self.assertEqual(census(g,m,s)["exact_twin_groups_excluding_generated"],0)
    def test_type_difference(self):
        g,m,s=self.fixture([self.row("A.a","A",typ=["Nat"]),self.row("B.b","B",typ=["Int"])])
        self.assertEqual(census(g,m,s)["exact_twin_groups_all"],0)
    def test_value_difference(self):
        g,m,s=self.fixture([self.row("A.a","A",val=["Nat.add"]),self.row("B.b","B",val=["Nat.mul"])])
        self.assertEqual(census(g,m,s)["exact_twin_groups_all"],0)
    def test_kernel_difference(self):
        g,m,s=self.fixture([self.row("A.a","A",ker=["Eq.refl"]),self.row("B.b","B",ker=["Eq.ndrec"])])
        self.assertEqual(census(g,m,s)["exact_twin_groups_all"],0)
    def test_digest_guard(self):
        g,m,_=self.fixture([self.row("A.a","A")])
        with self.assertRaisesRegex(ValueError,"digest mismatch"): census(g,m,"0"*64)
    def test_duplicate_guard(self):
        r=self.row("A.a","A"); g,m,s=self.fixture([r,r])
        with self.assertRaisesRegex(ValueError,"duplicate"): census(g,m,s)
    def test_ownership_guard(self):
        g,m,s=self.fixture([self.row("A.a","A")],modules="B\n")
        with self.assertRaisesRegex(ValueError,"ownership mismatch"): census(g,m,s)
    def test_generated_names(self):
        self.assertTrue(generated("New.a.eq_def"))
        self.assertTrue(generated("_private.New.a"))
        self.assertFalse(generated("New.a"))

def main():
    if "--self-test" in sys.argv:
        unittest.main(argv=[sys.argv[0]], verbosity=2); return
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("graph"); p.add_argument("modules"); p.add_argument("sha256")
    p.add_argument("output"); a=p.parse_args()
    result=census(a.graph,a.modules,a.sha256)
    Path(a.output).write_text(json.dumps(result,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
    print(json.dumps({k:v for k,v in result.items() if k!="candidates"},indent=2,ensure_ascii=False))

if __name__ == "__main__": main()
