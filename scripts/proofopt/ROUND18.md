# Round 18: exact single-site proof-value cut upper bounds

The previous shared signMatrix lemma experiment is not an original upstream contribution: upstream main bd15838ed6219289a212b94a70dde9e7281893a8 now independently contains a canonical lemma in CongruenceSubgroups, and both children use it. Keep round 17 as a historical experiment only; do not claim credit. The historical full rebuild was still running when inspected.

## Method and correctness

For each reachable project theorem other than the five immutable final roots, split its value edges through a private zero-weight gate. All type and kernel edges bypass the gate. Add a synthetic root connected to all five final roots. A project declaration contributes unit weight unless it is a final root. External declarations and gates have zero weight, but remain traversable.

A declaration becomes unreachable when a gate's outgoing edges are cut iff every original root-to-declaration path used the gate (equivalently, the gate dominates that declaration). Thus the weighted subtree of each gate in the immediate-dominator tree equals the exact loss under this counterfactual. The gate's owner is not deleted. Any real replacement of that one theorem's value, leaving the other declarations and ownership unchanged, adds references to this cut graph, so cannot remove more originally reachable project declarations than this bound. This is a bound, NOT a realizable proof or a certified optimization.

Compute all single-site bounds in one Lengauer-Tarjan dominator pass for the union and one per final root; no recursive traversal and no separate closure traversal for every candidate. CSR predecessors avoid per-edge objects. Recheck the top five positive union scores by independent explicit edge-cut traversals for every root and the union. The exact joint cut shows why independent scores may overlap or exhibit synergy. Zero individual gain does not rule out profitable joint changes.

## Reproduce

- node scripts/proofopt/value_cut.cjs --self-test
- node scripts/proofopt/dag_scope.cjs GRAPH.gz SHA256 SCOPE_DIR
- node --max-old-space-size=6144 scripts/proofopt/value_cut.cjs GRAPH.gz SHA256 SCOPE_DIR REPORT.json

The scope file digest and decompressed graph digest must match; recompute the five per-root reachability masks before ranking. The workflow uses the historical readable graph (887134 environment declarations; 220703 reachable; 49503 project excluding roots), not the original flagship baseline. It runs the CLI, all unit tests, and exact independent traversal checks. Output: histogram of every eligible theorem, top 40 positive targets, affected module samples, and joint cut of the top five. No module placement, dependency-type synthesis, or Lean proof modifications in this round. Analyze high-impact regions before selecting actual alternate mathematical proofs; the upper bound alone cannot establish feasibility.

The single-site model cannot measure DAG or CPU improvement. It does not account for coupled changes to other declarations; it excludes final roots, definitions and opaque declarations from editable sites by design. Report zero actual gains until independently measured. The optimizer and its CI are fork-only; do not include them in upstream source PRs.
