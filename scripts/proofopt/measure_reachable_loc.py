#!/usr/bin/env python3
"""Measure project-owned Lean LOC in the five-root reachable module closure.

This is deliberately a module-level upper bound: every project source file
owning at least one reachable declaration is counted in full. It does not
pretend to isolate declaration source spans. Nested Lean block comments and
line comments are excluded; strings are preserved as code.
"""
import gzip, json, argparse, unittest, tempfile
from pathlib import Path

ROOTS = [
    "riemannHypothesis",
    "riemannZeta_eq_zero_re",
    "LFunction_ne_zero_of_half_lt_re",
    "LFunction_eq_zero_re",
    "LFunction_eq_zero_re_of_isPrimitive",
]

def code_line_count(text):
    count = 0
    block = 0
    in_string = False
    escaped = False
    for line in text.splitlines():
        i = 0
        has_code = False
        while i < len(line):
            ch = line[i]
            nxt = line[i+1] if i+1 < len(line) else ""
            if block:
                if ch == "/" and nxt == "-":
                    block += 1; i += 2; continue
                if ch == "-" and nxt == "/":
                    block -= 1; i += 2; continue
                i += 1; continue
            if in_string:
                has_code = True
                if escaped: escaped = False
                elif ch == "\\": escaped = True
                elif ch == '"': in_string = False
                i += 1; continue
            if ch == "-" and nxt == "-":
                break
            if ch == "/" and nxt == "-":
                block = 1; i += 2; continue
            if ch == '"':
                in_string = True; has_code = True; i += 1; continue
            if not ch.isspace():
                has_code = True
            i += 1
        if has_code:
            count += 1
    if block:
        raise ValueError("unterminated Lean block comment")
    return count

def measure(graph_path, repo_root, expected_roots=ROOTS):
    rows = {}
    with gzip.open(graph_path, "rt", encoding="utf-8") as f:
        header = json.loads(next(f))
        if header.get("measurement") != "kernel-reference-graph":
            raise ValueError("unsupported graph measurement")
        for line in f:
            r = json.loads(line)
            if r.get("record") != "decl":
                continue
            name = r["name"]
            if name in rows:
                raise ValueError("duplicate declaration: " + name)
            rows[name] = r
    missing = sorted(set(expected_roots) - rows.keys())
    if missing:
        raise ValueError("missing target roots: " + ", ".join(missing))
    seen, todo = set(), list(expected_roots)
    while todo:
        name = todo.pop()
        if name in seen: continue
        if name not in rows:
            raise ValueError("unresolved dependency: " + name)
        seen.add(name)
        r = rows[name]
        for key in ("type", "kernel", "value"):
            todo.extend(r.get(key, []))
    modules = sorted({rows[n]["module"] for n in seen if rows[n].get("project")})
    files, missing_files = [], []
    for module in modules:
        path = Path(repo_root) / "src" / (module.replace(".", "/") + ".lean")
        if not path.is_file():
            missing_files.append(str(path))
            continue
        files.append({"module": module, "path":str(path.relative_to(repo_root)),
                      "nonblank_noncomment_lines":code_line_count(path.read_text(encoding="utf-8"))})
    if missing_files:
        raise ValueError("missing module source files: " + ", ".join(missing_files[:10]))
    return {
        "schema":1,
        "measurement":"five-root reachable project module LOC upper bound",
        "roots":list(expected_roots),
        "reachable_declarations":len(seen),
        "reachable_project_modules":len(modules),
        "source_files_counted":len(files),
        "project_owned_nonblank_noncomment_loc_upper_bound":sum(x["nonblank_noncomment_lines"] for x in files),
        "target_loc":2000,
        "scope_note":"Counts complete source files containing reachable project declarations. It is an upper bound, not exact declaration-span LOC; unrelated declarations in those files are included. Mathlib/TauCeti are excluded as external dependencies and must be reported separately.",
        "files":files,
    }

class Tests(unittest.TestCase):
    def test_blank_and_line_comments(self):
        self.assertEqual(code_line_count("a := 1\n\n-- hello\nb := 2\n"),2)
    def test_nested_block_comments(self):
        self.assertEqual(code_line_count("a := 1\n/- x\n/- nested -/\n-/\nb := 2\n"),2)
    def test_strings_preserved(self):
        self.assertEqual(code_line_count('a := " -- not a comment "\n'),1)
    def test_unterminated_comment_rejected(self):
        with self.assertRaises(ValueError): code_line_count("a := 1\n/- open")
    def test_multiple_lines_inside_string(self):
        self.assertEqual(code_line_count('a := "hello\nworld"\n'),2)

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--self-test",action="store_true")
    p.add_argument("--graph")
    p.add_argument("--repo",default=".")
    p.add_argument("--output",default="proofopt-loc.json")
    a=p.parse_args()
    if a.self_test:
        unittest.main(argv=[__file__],verbosity=2)
    else:
        if not a.graph: p.error("--graph is required")
        result=measure(a.graph,a.repo)
        Path(a.output).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
        print(json.dumps({k:v for k,v in result.items() if k!="files"},indent=2))

if __name__=="__main__": main()
