#!/usr/bin/env python3
"""Run bounded extraction commands in separate POSIX process groups."""
import argparse
import json
import os
import pathlib
import re
import signal
import subprocess
import tempfile

def run_case(command, cwd, seconds):
    p = subprocess.Popen(command, cwd=cwd, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, start_new_session=True)
    try:
        out, _ = p.communicate(timeout=seconds)
        return p.returncode, out.decode(errors="replace"), False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(p.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        out, _ = p.communicate()
        return p.returncode, out.decode(errors="replace"), True

def outcome(code, log, timeout, i):
    if timeout:
        return "inconclusive", None
    matches = re.findall(r"PROOFOPT_EXTRACT_(PASS|REJECT) (\d+)(?: |:|$)([^\n]*)", log)
    if code == 0 and len(matches) == 1 and int(matches[0][1]) == i:
        k, _, payload = matches[0]
        return ("pass", json.loads(payload.strip())) if k == "PASS" else ("reject", None)
    if not matches and re.search(r"maximum number of heartbeats|maximum recursion depth|deterministic.*timeout", log, re.I):
        return "inconclusive", None
    raise RuntimeError(f"unexpected Lean exit={code}, case={i}")

def main():
    p = argparse.ArgumentParser()
    p.add_argument("report", type=pathlib.Path)
    p.add_argument("lean", type=pathlib.Path)
    p.add_argument("base", type=pathlib.Path)
    p.add_argument("output", type=pathlib.Path)
    p.add_argument("--seconds", type=int, default=90)
    a = p.parse_args()
    report = json.loads(a.report.read_text())
    header = "import Main\n" + a.lean.read_text()
    a.output.mkdir(parents=True, exist_ok=True)
    results = []
    with tempfile.TemporaryDirectory() as d:
        for i, pair in enumerate(report["pairs"]):
            if pair["index"] != i or not all(re.fullmatch(r"[A-Za-z][A-Za-z0-9_']*(\.[A-Za-z][A-Za-z0-9_']*)*", pair[k]) for k in ("left", "right")):
                raise ValueError("invalid pair")
            case = pathlib.Path(d) / f"Case{i}.lean"
            command = f'#proofopt_extract {i} {json.dumps(pair["left"])} {json.dumps(pair["right"])}'
            case.write_text(header + "\n" + command + "\n")
            code, log, timeout = run_case(["lake", "env", "lean", str(case)], a.base, a.seconds)
            (a.output / f"case-{i}.log").write_text(log)
            status, payload = outcome(code, log, timeout, i)
            results.append({"index": i, "left": pair["left"], "right": pair["right"], "outcome": status, "payload": payload})
            print(f"case {i}: {status}", flush=True)
    cert = {k: report[k] for k in ("schema", "input_sha256", "scope_sha256")}
    cert["results"] = results
    (a.output / "cert.json").write_text(json.dumps(cert, indent=2) + "\n")

if __name__ == "__main__":
    main()
