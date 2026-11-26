# Round 07 — isolated proof-only candidate and paired validation runner

The research tools stay on `proofopt/global-import-graph-v1`. A separate branch
`proofopt/round05-proof-only` contains exactly the round-05 mathematical source
candidate relative to the fixed baseline. It is **not** a new mathematical
optimization or a compiled PR. No formal PR is opened. See baseline_round07.json
for exact SHA identities, scope checks, and test results.

The upstream main returned by the connector no longer contains the old
VwinOfRow path; comparison with the locked baseline returned "No common
ancestor". Do not auto-rebase or treat this as a measured upstream improvement.

## Run on a capable trusted Linux host

Use a sandbox/VM as upstream advises; the proof executes code. The runner
requires Python 3.9+ on Linux, Git, the pinned Lean/Lake and ample disk and RAM.
Run from a clone that has the research branch and proof-only branch, with both
commit objects available. Choose new output directories outside the checkout.
Worktrees and logs are retained for audit; clean them manually after review.

```bash
B=91b273530883b723ef4422436e0dc3557749325a
C=fef5d8c31f796acf271b1754008b822b841818eb
T=scripts/proofopt/verify_pair.py
python3 -m unittest discover -s scripts/proofopt -p test_verify_pair.py
python3 "$T" plan --repo . --base "$B" --candidate "$C"
python3 "$T" incremental --repo . --base "$B" --candidate "$C" --jobs 4 --out /scratch/po-incremental
python3 "$T" clean --repo . --base "$B" --candidate "$C" --jobs 4 --out /scratch/po-clean
python3 "$T" comparator --repo . --base "$B" --candidate "$C" --jobs 4 --out /scratch/po-comparator
```

The plan rejects moving refs, non-ancestral pairs and anything except the
single approved proof-file diff; it verifies ten protected and configuration
blobs. Incremental validation fetches baseline project cache, checks its
availability, switches to the exact candidate, and runs a real full default
Lake build. Clean mode creates two separate fresh worktrees, uses the upstream
Mathlib-only cache instruction and disables Lake artifact cache. CPU is the
waited child user+system time for the build step, excluding cache setup.
Comparator mode runs the upstream command for both fresh worktrees, separately
from CPU measurement. The runner records exit codes, logs, machine, requested
LEAN_NUM_THREADS, toolchain, and exact source identities, and preserves failures.

The test suite uses real local Git commits/worktrees and mock Lake and bubblewrap
executables. It exercises the three run modes, failure and scope guards. It does
not establish actual Lean success, cache availability, effective thread counts,
or CPU savings. Confirm actual Lake thread settings and machine isolation,
repeat paired runs (including reverse order), and report variability before
counting the CPU result toward the flagship target. For DAG and declaration
metrics use the prior capture/export and disk metrics tools separately after
real builds; no full-project export is available now. The proof-only branch
must not be proposed upstream until the current upstream history and build
have been reconciled.
