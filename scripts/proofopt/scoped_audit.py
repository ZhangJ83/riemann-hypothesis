#!/usr/bin/env python3
"""Strict certificate diagnostics. Never promote local counts to global metrics."""
import argparse
import json
import pathlib
import re
import unittest

def check_payload(p):
    if not isinstance(p, dict):
        raise ValueError("missing payload")
    for k, lo, hi in [("holeCount", 0, 4), ("scopeArity", 0, None)]:
        v = p.get(k)
        if type(v) is not int or v < lo or (hi is not None and v > hi):
            raise ValueError("invalid " + k)
    for k in ("localRawDagBefore", "localRawDagAfter"):
        if k not in p:
            raise ValueError("missing " + k)
        v = p[k]
        if v is not None and (type(v) is not int or not 0 < v <= 200000):
            raise ValueError("invalid " + k)
    a, b = p["localRawDagBefore"], p["localRawDagAfter"]
    return None if a is None or b is None else a-b

def fixtures(log):
    found = {}
    for m in re.finditer(r"PROOFOPT_EXTRACT_(PASS|REJECT) (\d+)(?: |:)([^\n]*)", log):
        status, i, payload = m.groups()
        i = int(i)
        if i in found:
            raise ValueError("duplicate fixture")
        found[i] = (status, json.loads(payload) if status == "PASS" else None)
    expected = {0: (2, 4), 1: (2, 4), 2: (0, 1)}
    if set(found) != set(range(6)):
        raise ValueError("fixture IDs")
    for i, (holes, arity) in expected.items():
        status, p = found[i]
        if status != "PASS" or p["holeCount"] != holes or p["scopeArity"] != arity:
            raise ValueError("wrong exact fixture " + str(i))
        check_payload(p)
    if any(found[i][0] != "REJECT" for i in (3, 4)) or found[5][0] != "PASS":
        raise ValueError("unexpected search outcome")
    check_payload(found[5][1])
    return {"fixture_pass": 4, "fixture_reject": 2}

def report(cert, replay):
    for k in ("schema", "input_sha256", "scope_sha256"):
        if cert[k] != replay[k]:
            raise ValueError("provenance")
    if len(cert["results"]) != len(replay["results"]):
        raise ValueError("count")
    out = []
    for a, b in zip(cert["results"], replay["results"]):
        for k in ("index", "left", "right", "outcome"):
            if a[k] != b[k]:
                raise ValueError("certificate/replay mismatch")
        if a["outcome"] not in ("pass", "reject", "inconclusive"):
            raise ValueError("unknown outcome")
        if a["outcome"] != "pass":
            if a["payload"] is not None or b["model"] is not None:
                raise ValueError("nonpass payload")
            continue
        p = a["payload"]
        local = check_payload(p)
        model = b["model"]
        net = model["net"] if model and model["status"] == "modeled" else None
        if net is not None and (type(net) is not int or model["before"]-model["after"] != net):
            raise ValueError("invalid net")
        out.append({"index": a["index"], "left": a["left"], "right": a["right"],
                    "hole_count": p["holeCount"], "scope_arity": p["scopeArity"],
                    "local_raw_expr_dag_delta": local,
                    "model_dependency_delta": net,
                    "model_status": model["status"] if model else None,
                    "nonregressing_model_positive_local": net is not None and net >= 0 and
                        local is not None and local > 0})
    return {"schema": 1, "input_sha256": cert["input_sha256"],
            "scope_sha256": cert["scope_sha256"],
            "attempted": len(cert["results"]), "kernel_certified": len(out),
            "bounded_no_certificate": sum(a["outcome"]=="reject" for a in cert["results"]),
            "inconclusive": sum(a["outcome"]=="inconclusive" for a in cert["results"]),
            "multi_hole_certified": sum(a["hole_count"]>=2 for a in out),
            "open_scope_certified": sum(a["scope_arity"]>0 for a in out),
            "model_positive": sum(a["model_dependency_delta"] is not None and
                                  a["model_dependency_delta"]>0 for a in out),
            "candidates": out, "actual_dependency_reduction": None,
            "actual_global_dag_reduction": None, "actual_cpu_reduction": None}

class Tests(unittest.TestCase):
    def payload(self):
        return {"holeCount":2,"scopeArity":4,"localRawDagBefore":10,"localRawDagAfter":7}
    def data(self):
        p = self.payload()
        a = {"index":0,"left":"A","right":"B","outcome":"pass"}
        common = {"schema":1,"input_sha256":"g","scope_sha256":"s"}
        return ({**common,"results":[{**a,"payload":p}]},
                {**common,"results":[{**a,"model":{"status":"modeled","before":5,"after":5,"net":0}}]})
    def test_positive(self):
        a,b=self.data(); x=report(a,b)
        self.assertEqual(x["multi_hole_certified"],1)
        self.assertEqual(x["open_scope_certified"],1)
        self.assertEqual(x["model_positive"],0)
        self.assertTrue(x["candidates"][0]["nonregressing_model_positive_local"])
        self.assertIsNone(x["actual_global_dag_reduction"])
    def test_bad(self):
        for k,v in [("holeCount",5),("scopeArity",True),("localRawDagBefore",0),("localRawDagAfter",200001)]:
            with self.subTest(k=k):
                p=self.payload(); p[k]=v
                with self.assertRaises(ValueError): check_payload(p)
        a,b=self.data(); b["scope_sha256"]="other"
        with self.assertRaises(ValueError): report(a,b)
        a,b=self.data(); b["results"][0]["model"]["net"]=1
        with self.assertRaises(ValueError): report(a,b)
        a,b=self.data(); b["results"][0]["left"]="C"
        with self.assertRaises(ValueError): report(a,b)
    def test_unknown(self):
        p=self.payload(); p["localRawDagAfter"]=None
        self.assertIsNone(check_payload(p))
        a,b=self.data(); b["results"][0]["model"]={"status":"cycle"}
        self.assertFalse(report(a,b)["candidates"][0]["nonregressing_model_positive_local"])
    def test_fixtures(self):
        lines=[]
        for i,h,s in [(0,2,4),(1,2,4),(2,0,1),(5,2,4)]:
            p=self.payload(); p.update(holeCount=h,scopeArity=s)
            lines.append(f"PROOFOPT_EXTRACT_PASS {i} "+json.dumps(p))
        lines += ["PROOFOPT_EXTRACT_REJECT 3: bad", "PROOFOPT_EXTRACT_REJECT 4: bad"]
        log="\n".join(lines)
        self.assertEqual(fixtures(log),{"fixture_pass":4,"fixture_reject":2})
        with self.assertRaises(ValueError): fixtures(log+"\n"+lines[0])
        with self.assertRaises(ValueError): fixtures("\n".join(lines[:-1]))

if __name__=="__main__":
    import sys
    if sys.argv[1:]==["--self-test"]:
        unittest.main(argv=[sys.argv[0]])
    else:
        p=argparse.ArgumentParser()
        p.add_argument("mode",choices=("fixtures","report"))
        p.add_argument("paths",nargs="+",type=pathlib.Path)
        a=p.parse_args()
        if a.mode=="fixtures":
            if len(a.paths)!=1: p.error("one log required")
            print(json.dumps(fixtures(a.paths[0].read_text())))
        else:
            if len(a.paths)!=3: p.error("cert replay output required")
            x=report(*[json.loads(z.read_text()) for z in a.paths[:2]])
            a.paths[2].write_text(json.dumps(x,indent=2)+"\n")
            print(json.dumps(x))
