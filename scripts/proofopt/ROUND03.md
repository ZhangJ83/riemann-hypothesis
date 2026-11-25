# Round 03: kernel reference graph and exact replacement planning

Fork-only research tooling, not an upstream proof patch.

Baseline: 91b273530883b723ef4422436e0dc3557749325a; Lean v4.37.0-rc1; Mathlib 31ce06eaadf4a200c0e1407c5f10953cf606b8f8.
The graph is oriented declaration -> referenced constant. Type references and inductive/constructor/recursor metadata are immutable. Theorem value reference sets are replaceable in the model only; roots cannot be edited. All nodes including external dependencies are traversed, and only project-owned reachable nodes are counted. Existing unreachable nodes are not counted as savings. Unknown references, stale replacement sets and new reachable axioms fail closed. Distinct alternatives for one declaration are mutually exclusive. The exact search enumerates budget-feasible combinations; exceeding the state limit raises an error, never a false certificate.

## Reproduce tests
```sh
node scripts/proofopt/kernel_graph_cli.mjs test scripts/proofopt/main_projection.json
```
The test fixture is a **partial source projection**, not a Lean export; only the four explicit references among the five root declarations in the pinned Main.lean are represented. The tests were executed in V8 using the same JavaScript functions committed here, not via Node CLI.

## Export actual Lean graph (not yet run)
From a checkout of the fixed baseline with compiled Main and the scripts copied from this development branch:
```sh
python3 -c 'from pathlib import Path; print("\\n".join(".".join(p.relative_to("src").with_suffix("").parts) for p in sorted(Path("src").rglob("*.lean"))))' > /tmp/proofopt-modules.txt
lake env lean --run scripts/proofopt/KernelGraph.lean /tmp/proofopt.jsonl /tmp/proofopt-modules.txt riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive
node scripts/proofopt/kernel_graph_cli.mjs inspect /tmp/proofopt.jsonl
```
The extractor is an uncompiled candidate. It explicitly follows Expr constructors, projection type names, declaration types/values (including opaque values), and inductive/recursor metadata. The quotient/builtin policy and the handling of private declarations must be reconciled against leanexport/Comparator before accepting a flagship baseline. Unknown dependencies cause the JS loader to reject the snapshot. No actual kernel closure, expression DAG size, build CPU savings or theorem correctness is established by this round. A graph replacement is a hypothesis about a future kernel-checked proof, not a legal Lean transformation.

Candidate JSON array format: `[{"id":"example","decl":"existing theorem","before":["old dependency"],"after":["new dependency"],"cost":1}]`. The before set must exactly match the extracted value-reference set. Optimize with `node scripts/proofopt/kernel_graph_cli.mjs optimize graph.jsonl candidates.json 10 100000`. The algorithm is exact only within this finite fixed graph and candidate model; it does not construct proofs or claim novelty for exhaustive search.
