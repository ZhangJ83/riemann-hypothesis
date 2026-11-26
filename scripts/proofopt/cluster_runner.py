#!/usr/bin/env python3
"""Run isolated triple certificates; bind exact selection bytes to the result."""
import argparse
import hashlib
import json
import pathlib
import re
import tempfile
import unittest
from extract_runner import run_case, outcome

NAME = re.compile(r"[A-Za-z][A-Za-z0-9_']*(\.[A-Za-z][A-Za-z0-9_']*)*")

def cluster_command(i, cluster):
    owners = cluster["owners"]
    if cluster["index"] != i or len(owners) != 3 or len(set(owners)) != 3 or not all(NAME.fullmatch(n) for n in owners):
        raise ValueError("invalid cluster")
    return f'#proofopt_cluster {i} ' + " ".join(json.dumps(n) for n in owners)

def fixture_check(log):
    seen = {}
    for m in re.finditer(r"PROOFOPT_EXTRACT_(PASS|REJECT) (\d+)(?: |:)([^\n]*)", log):
        k, i, p = m.groups()
        i = int(i)
        if i in seen:
            raise ValueError("duplicate fixture")
        seen[i] = (k, json.loads(p) if k == "PASS" else None)
    if set(seen) != set(range(6)):
        raise ValueError("missing fixture")
    for i, expected in {0:(2,4,0), 1:(2,6,0), 2:(0,3,2)}.items():
        status, p = seen[i]
        if status != "PASS" or p["ownerCount"] != 3 or tuple(p[k] for k in ("holeCount","scopeArity","usedScopeArity")) != expected:
            raise ValueError("incorrect abstraction " + str(i))
    if any(seen[i][0] != "REJECT" for i in (3,4)) or seen[5][0] != "PASS":
        raise ValueError("incorrect search outcome")
    return {"pass":4,"reject":2}

def execute(a):
    raw = a.report.read_bytes()
    report = json.loads(raw)
    header = "import Main\n" + a.lean.read_text()
    a.output.mkdir(parents=True, exist_ok=True)
    results = []
    with tempfile.TemporaryDirectory() as d:
        for i, cluster in enumerate(report["clusters"]):
            case = pathlib.Path(d) / f"Case{i}.lean"
            case.write_text(header + "\n" + cluster_command(i, cluster) + "\n")
            code, log, timeout = run_case(["lake","env","lean",str(case)], a.base, a.seconds)
            (a.output / f"case-{i}.log").write_text(log)
            status, payload = outcome(code, log, timeout, i)
            results.append({"index":i,"owners":cluster["owners"],"outcome":status,"payload":payload})
            print(f"cluster {i}: {status}", flush=True)
    cert = {k:report[k] for k in ("schema","input_sha256","scope_sha256")}
    cert.update(selection_sha256=hashlib.sha256(raw).hexdigest(), results=results)
    (a.output / "cert.json").write_text(json.dumps(cert,indent=2)+"\n")

class Tests(unittest.TestCase):
    def test_command(self):
        self.assertEqual(cluster_command(0,{"index":0,"owners":["A","B.C","D"]}),'#proofopt_cluster 0 "A" "B.C" "D"')
        for x in [["A","A","B"],["A","B","C\n"],["A","B"]]:
            with self.assertRaises(ValueError): cluster_command(0,{"index":0,"owners":x})
    def test_outcome(self):
        self.assertEqual(outcome(-9,"",True,0),("inconclusive",None))
        self.assertEqual(outcome(0,"PROOFOPT_EXTRACT_REJECT 0: no",False,0),("reject",None))
        with self.assertRaises(RuntimeError): outcome(0,"PROOFOPT_EXTRACT_REJECT 1: no",False,0)
    def test_fixture_parser(self):
        lines=[]
        for i,h,s,u in [(0,2,4,0),(1,2,6,0),(2,0,3,2),(5,2,4,0)]:
            lines.append(f"PROOFOPT_EXTRACT_PASS {i} "+json.dumps({"ownerCount":3,"holeCount":h,"scopeArity":s,"usedScopeArity":u}))
        lines += ["PROOFOPT_EXTRACT_REJECT 3: no","PROOFOPT_EXTRACT_REJECT 4: no"]
        self.assertEqual(fixture_check("\n".join(lines)),{"pass":4,"reject":2})
        with self.assertRaises(ValueError): fixture_check("\n".join(lines+[lines[0]]))
        with self.assertRaises(ValueError): fixture_check("\n".join(lines[:-1]))

if __name__=="__main__":
    import sys
    if sys.argv[1:]==["--self-test"]:
        unittest.main(argv=[sys.argv[0]])
    elif len(sys.argv)==3 and sys.argv[1]=="fixtures":
        print(json.dumps(fixture_check(pathlib.Path(sys.argv[2]).read_text())))
    else:
        p=argparse.ArgumentParser()
        for k in ("report","lean","base","output"): p.add_argument(k,type=pathlib.Path)
        p.add_argument("--seconds",type=int,default=90)
        execute(p.parse_args())
