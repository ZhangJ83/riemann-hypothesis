# Round 21: exact candidate-boundary quotient

The previous job 45839458205 passed fixtures, but real certification failed:
five explicit apply rejects and five heartbeat timeouts. Timeouts are not
mathematical rejections. The isolated runner preserves the distinction and
fails closed on any unexpected process failure.

For each root and every candidate gate's default/replacement outgoing set,
traverse the graph stopping at candidate gates. For each vertex record the
bitmask of sources reaching it. For a configuration, saturate active sources:
start from roots and activate the chosen option at every reached gate.
A vertex is reachable iff its mask intersects the saturated source set
(split any path at the candidate gates; conversely concatenate the segments).
Aggregate weights by mask. This is exact for finite directed graphs,
including cycles, not a dominator approximation. Retain zero-gain candidates
and enumerate joint configurations with one replacement per owner.
The direct traversal checks every singleton and the chosen union/per-root
closures. Exhaustive search is certified only within the state budget;
the fallback is explicitly nonoptimal. The 30-source mask limit fails closed.

Tests: node scripts/proofopt/joint.cjs; node scripts/proofopt/parametric.cjs --self-test.
A two-root fixture has zero individual gain but one joint saved declaration.
320 random cyclic graphs and 8,640 configurations are compared with direct
reachability, separately for each root and union. This is a counterfactual
graph optimization, not actual source rewriting or measured proof DAG/CPU
savings. No upstream proof or challenge file changes. The historical artifact
is distinct from the original flagship baseline and current upstream main.
