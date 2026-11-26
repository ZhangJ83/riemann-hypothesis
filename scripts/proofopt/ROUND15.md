# Round 15: bounded structural anti-unification

The pass consumes an exact DAG export with topologically ordered node records
`["n", id, tag, atom, children]` followed by theorem records
`["r", name, module, typeId, proofId, universeParameters]`.
Atoms encode constructor payloads; binder names/annotations are already erased by
Round 14's quotient. IDs are snapshot-local. The exporter samples project
theorems by name hash modulo 16; all descendants of sampled types and proofs
are included, with a fail-closed 1.5M-node limit.

For each pair with matching head signatures and ordered universe parameters,
jointly traverse the type and proof DAGs. Exact equal subtrees become references;
equal constructors recurse; differing closed subtrees become holes. Repeated
ordered mismatch pairs share one hole. Loose de Bruijn indices are computed
bottom-up (binder scopes differ for let values and bodies). Open mismatches
are rejected, as are whole-proof holes, exact duplicates and exceeded budgets.
The same substitution is shared across type and proof. Reconstruct both
original DAGs via structural lookup and require the original root IDs.

Discovery uses cross-module pairs in a bounded deterministic name window.
Ranking counts rigid constructor matches and holes, not estimated actual
compression. Report omitted pairs, rejection reasons and global budget status.
The algorithm is conservative, does not infer hole types or dependency order,
and does not generate Lean declarations. Exact syntax reconstruction is NOT
kernel validation. No flagship savings are recorded. Next step: typed hole
abstraction and kernel-checked replacements, then rerun global measurements.

## Reproduce
```sh
node scripts/proofopt/anti_unify.cjs --self-test
node scripts/proofopt/anti_unify.cjs sample.jsonl report.json
```
The dedicated workflow first restores the historical pinned cache and reproduces
the Round 14 scope audit, then emits the sample and runs discovery. It does
not modify protected proof/challenge files. Original baseline remains locked.
