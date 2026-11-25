# Round 05 — scoped proof-body bypass candidate

This is a **candidate** on the research fork, not a kernel-checked optimization.
No declarations are deleted and no theorem headers, imports, or Comparator challenge
files are modified. The source pass deliberately targets two named clump members and
nine named callers in VwinOfRow.lean; it is not a general Lean parser.

## Method
A single qualified constant RHS with the explicit OpenImageCondition binder unused
is a source-level candidate for typed bypass at explicit calls. The replacement is
`(show ResultType from UnderlyingConstant)`, retaining the expected result type.
The pass rejects unexpected caller layouts and comments in rewritten bodies. This
does not prove elaboration, resolution, or kernel equivalence: those must be checked
on the changed file and all downstream modules. Do not remove public wrappers without
checking all references. The source grows, so only a measured kernel dependency/DAG
improvement would count.

## Reproduce
From a clone of this fork:
```bash
P='src/Development/AutomorphicArithmetic/AutomorphicVarieties/ModularityArgument/ThresholdArguments/DenseThresholdCases/VwinOfRow.lean'
git show 9893a30525b5e76ed9bd856c1493cb7a3fe2aab5:"$P" > /tmp/po-before.lean
git show 756a70250dcba9162b99d4ea35c186558434c17e:"$P" > /tmp/po-upstream.lean # fetch upstream ref first if absent
node scripts/proofopt/test_open_wrapper_pass.mjs /tmp/po-before.lean /tmp/po-upstream.lean
node scripts/proofopt/open_wrapper_cli.mjs /tmp/po-before.lean /tmp/po-after.lean /tmp/po-report.json
cmp /tmp/po-after.lean "$P"
```
The exact functions were run in V8 on both pinned GitHub blobs, not via Node CLI.
17 checks passed. Source observations: 25 eligible wrappers, 22 affected wrappers,
33 explicit call sites, nine proof bodies. The 22 affected full names occur just
once in the changed file; unqualified or other-file references have not been ruled out.

## Validation on a capable Linux machine
Use separate clean worktrees for the fixed proof baseline and candidate; do not
change protected files or compare against a moving main. Fetch the project cache
for an incremental candidate check, then run lake build (not --no-build) so the
changed module and all importers are checked. If the cached candidate is missing,
do not treat this as passing. After compiling, run capture_export.sh in both
worktrees, compare with the same metrics implementation and explicit ownership,
then run Comparator from a clean, trusted challenge environment. For clean build
CPU comparison, use the same machine, toolchain, thread count, cache policy and
fresh proof build directory, with only Mathlib's official cache restored as
specified in upstream README. Record both user and system CPU and exit status.
A cache-based validation is not a clean-build benchmark.

Upstream verification/NOTES.md reports historical full exports around 61.57 GB
and exporter peak memory around 163 GB (different revision). The current JS
interner is not yet demonstrated at that scale. A disk-backed or sharded
measurement implementation and actual large runner are prerequisites for full
metrics; do not assert any savings before those checks. See baseline_round05.json
for the pinned source identity and test outcomes.
