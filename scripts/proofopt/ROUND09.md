# Round 09: closed-prefix wrapper simulation

The pass recognizes a theorem whose type and proof begin with aligned forall/lambda binders, and whose remaining type and value are closed. The shortest such prefix is removed only at fully applied occurrences in editable reachable monomorphic theorem values. Closed bodies can be reused under binders without lifting. No arbitrary dependent substitution or Lean source emission. The structural interner is unchanged; a wrapper records its keys for reconstruction. Original declaration types, roots and metadata remain intact. Every plan must preserve each root's reachable declaration subset, avoid new axioms and avoid increases in the four union metrics. Search is exact only over enumerated active rule subsets, with a hard cap; no proof of novelty or kernel correctness.

Reproduce with Node 22+ and the pinned lean4export fixture recorded in baseline_round09.json:

    node scripts/proofopt/test_closed_wrapper.mjs /path/to/Nat.add_succ.ndjson
    node scripts/proofopt/closed_wrapper_cli.mjs /path/to/Nat.add_succ.ndjson - 2 4096 Nat.add_succ

Tests here ran in V8; Node file I/O, ownership input CLI, RH-scale data and Lean elaboration remain untested. Synthetic extension is not a kernel-checked export. The result is a candidate ranking, not a source rewrite or verified mathematical contribution. Use a compiled candidate and independent verifier before accepting any rewrite.
