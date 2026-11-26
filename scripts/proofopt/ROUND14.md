# Round 14: exact expression DAG census

Round 13 completed successfully, but its joint counterfactual saved only 3 of
49,503 historical project dependencies (0.00606%), and was not typechecked.
Two wrappers were already removed upstream. Exact reference signatures alone
are not a plausible route to the 20% flagship target.

This round adds a kernel Expr measurement subsystem, not a proof rewrite.
It separates three categories: all imported reachable expressions, project-owned
reachable expressions, and project theorem values. Each category has per-root
and five-root union counts. A single interned node may belong to multiple
roots and categories. The quotient is specified in baseline_round14.json.
No digest collision can merge keys; Lean HashMap uses structural key equality.
Node IDs are run-local and must not be compared across runs.

The scope generator validates the historical graph SHA256 and includes all type,
value, and kernel metadata edges. It computes each root's reachability
independently and assigns bitsets. KernelDag checks name uniqueness, scope
coverage and project-module membership against imported Main. It counts recursor
rule RHS expressions too. It refuses missing theorem/definition bodies but
reports missing opaque bodies. An unavailable body means the corresponding
metric is partial. No independent kernel check or exact current-upstream
baseline is claimed.

Reproduce:
- node scripts/proofopt/dag_scope.cjs --self-test
- node scripts/proofopt/dag_scope.cjs GRAPH.jsonl.gz SHA256 OUTPUT_DIR
- lake env lean scripts/proofopt/KernelDag.lean
- lake env lean --run scripts/proofopt/KernelDag.lean --self-test
- lake env lean --tstack=400000 --run scripts/proofopt/KernelDag.lean DAG.json SCOPE.tsv MODULES.txt ROOT...
- See the dedicated Actions workflow for pinned cache restore and cross-checks.

Type-and-value twin groups require identical normalized type and value roots
and identical ordered universe parameter lists. They remain candidates:
visibility, substitutions, theorem types, kernel checking and global net
benefit must be established separately. Syntactically equal subexpressions
under different local contexts are not automatically extractable as lemmas.

The original baseline, historical readable base, and current upstream main
are distinct. No formal compression percentage is inferred from any historical
census. The fork branch intentionally contains only research tooling; upstream
contributions must be focused proof edits without these unrelated files.
