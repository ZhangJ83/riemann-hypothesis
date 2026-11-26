#!/usr/bin/env python3
"""Isolate every Lean command so resource exhaustion cannot erase other outcomes."""
import argparse
import json
import pathlib
import re
import subprocess
import tempfile

def main():
    p = argparse.ArgumentParser()
    p.add_argument("report", type=pathlib.Path)
    p.add_argument("rendered", type=pathlib.Path)
    p.add_argument("base", type=pathlib.Path)
    p.add_argument("output", type=pathlib.Path)
    p.add_argument("--seconds", type=int, default=120)
    args = p.parse_args()
    report = json.loads(args.report.read_text())
    lines = args.rendered.read_text().splitlines()
    commands = [x for x in lines if x.startswith("#proofopt_param ")]
    header = "\n".join(x for x in lines if not x.startswith("#proofopt_param "))
    if len(commands) != len(report["candidates"]):
        raise ValueError("candidate count mismatch")
    args.output.mkdir(parents=True, exist_ok=True)
    outcomes = []
    with tempfile.TemporaryDirectory() as d:
        for i, (command, c) in enumerate(zip(commands, report["candidates"])):
            if c["index"] != i or not command.startswith(f"#proofopt_param {i} "):
                raise ValueError("index mismatch")
            path = pathlib.Path(d) / f"Case{i}.lean"
            path.write_text(header + "\n" + command + "\n")
            refs = None
            try:
                run = subprocess.run(["lake", "env", "lean", str(path)],
                                     cwd=args.base, stdout=subprocess.PIPE,
                                     stderr=subprocess.STDOUT, text=True,
                                     timeout=args.seconds)
                log = run.stdout
                matches = re.findall(r"PROOFOPT_PARAM_(PASS|REJECT) (\d+)(?: |:|$)([^\n]*)", log)
                if run.returncode == 0 and len(matches) == 1 and int(matches[0][1]) == i:
                    kind, _, payload = matches[0]
                    outcome = "pass" if kind == "PASS" else "reject"
                    if outcome == "pass":
                        refs = json.loads(payload.strip())
                        if not isinstance(refs, list) or not all(isinstance(v, str) for v in refs) or c["target"] not in refs:
                            raise ValueError("malformed certificate")
                        refs = sorted(set(refs))
                elif re.search(r"maximum number of heartbeats|maximum recursion depth|deterministic\\?\)? timeout", log, re.I) and not matches:
                    outcome = "inconclusive"
                else:
                    (args.output / f"case-{i}.log").write_text(log)
                    raise RuntimeError(f"unrecognized Lean failure for candidate {i}, exit={run.returncode}")
            except subprocess.TimeoutExpired as e:
                log = (e.stdout or b"")
                if isinstance(log, bytes):
                    log = log.decode(errors="replace")
                log += "\nPROOFOPT_RESOURCE_LIMIT: wall timeout\n"
                outcome = "inconclusive"
            (args.output / f"case-{i}.log").write_text(log)
            outcomes.append({"index": i, "source": c["source"], "target": c["target"],
                             "outcome": outcome, "refs": refs})
            print(f"candidate {i}: {outcome}", flush=True)
    cert = {"schema": 1, "input_sha256": report["input_sha256"],
            "scope_sha256": report["scope_sha256"], "results": outcomes}
    (args.output / "cert.json").write_text(json.dumps(cert, indent=2) + "\n")

if __name__ == "__main__":
    main()
