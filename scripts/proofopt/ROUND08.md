# Exact-type theorem alias optimization (round 8)

This pass groups **monomorphic safe theorems** by identical structural-v1 types. It simulates replacing a non-root, project-owned reachable theorem's proof by another theorem of identical type, retaining its name and type. It does not unfold definitions or modify source. The candidate search enumerates every subset within the budget with at most one edit per source; it rejects cycles even in edited nodes not reachable from the roots. It refuses to run if the exact state count exceeds the bound. It requires no regression in any union metric and no new reachable axiom per root. The lexicographic objective prioritizes project declaration count, then total declarations, combined DAG, and value DAG. Without ownership, only total declarations are measured.

This is a simulated optimization, not a Lean kernel check. Structural equality under the existing normalization is a conservative candidate filter, not a substitute for type checking. Universe-polymorphic theorems, definitions, inductives, general anti-unification, and rewriting caller expressions are outside scope. The in-memory interner remains a scale limitation. No actual RH proof was changed by this pass.

## Reproduction

Fetch the genuine sample at https://github.com/leanprover/lean4export/blob/df81913eee5519d5a88ae5b0fd701b5298cc29ab/examples/Nat.add_succ.ndjson and save it outside the source checkout. Git blob SHA: d3cd35f1313b4e78b5fded9886e450112aa75def.

    node scripts/proofopt/run_alias_tests.mjs /path/to/Nat.add_succ.ndjson
    node scripts/proofopt/alias_optimizer_cli.mjs /path/to/Nat.add_succ.ndjson - 2 100000 Nat.add_succ

Tests executed using V8 with the module wrappers adapted in memory. The command-line entrypoints themselves have not been executed in Node. The real sample has no eligible alias pair; the positive test extends it in memory with hypothetical monomorphic theorem aliases and is not an independently verified Lean export. Random tests use graph-only fixtures. See baseline_round08.json for actual results and limits.
