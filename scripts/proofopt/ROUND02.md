# ProofOpt: joint support planner (Round 02)

Fork-only research tooling; do not include these files in an upstream proof PR.

## Model and exact algorithm

For each historical constant c, let T(c) be the set of structures associated
with it in field-reach.tsv. A selected set S receives one unit of proxy credit
for c iff T(c) is a subset of S. Aggregate equal supports into weights w(T).
These are *not* certified kernel dependency cuts: the field-reach associations
come from a historical all-fields analysis, and selecting all associated
structures is neither a proven sufficient nor necessary condition for a legal
Lean rewrite. Unit cost per structure is a planning assumption, not CPU cost.

The support hypergraph decomposes into connected components. Every weighted
support lies entirely within one component, so objective values add across
components. Within a component, subset zeta transform gives the value for
every subset; retain the maximum at each exact cardinality. Max-plus
convolution of these local frontiers gives the global optimum for every
budget. Backtracking reconstructs the selected set and independently
recomputes its objective. Because all weights are positive, the optimum for
exact cardinality k is also the optimum for at most k (extra candidates can
only preserve/increase the model objective). Exactness applies only to this
model and the component-size cap. Larger components are rejected, not silently
approximated. Complexity: sum O(n_i 2^n_i) local time, O(N^2) convolution
time and O(N^2) reconstruction space as implemented.

## Reproduce

From scripts/proofopt/:
```sh
python3 -m unittest -v test_joint_support
python3 joint_support.py --fixture historical_fixture.json --budget 232 --output report.json
curl -L https://raw.githubusercontent.com/righi/riemann_fieldlive/3ef0ba5b002bbfe06e22a7860a44d0bb9c85bf98/results/v4.37-fcb6eac753/field-reach.tsv -o field-reach.tsv
python3 joint_support.py --field-reach field-reach.tsv --expect-blob 7c26d8ab76b15c0a4f84bd6d1aca0188e17fb137 --budget 232 --output named-report.json
```

The fixture is the weighted support hypergraph aggregated from the pinned
source, with identifiers anonymized. It preserves exact optimal scores, not
the original candidate identities or tie-breaking order of greedy search.
Independent JavaScript analysis of the named TSV and Python tests on the
fixture agreed on optimum checkpoints. Python: 12/12 tests, including 144
seeded random exhaustive-oracle comparisons, CLI JSON and historical fixture.

Historical source: https://github.com/righi/riemann_fieldlive/blob/3ef0ba5b002bbfe06e22a7860a44d0bb9c85bf98/results/v4.37-fcb6eac753/field-reach.tsv

862 candidate structures, 2449 fields, 4062 distinct associated constants,
583 weighted support sets, 760 components (largest 14), 22528 component
subsets. Named greedy score at budget 232: 3527; optimum: 3605 (78 more).
These are proxy counts, not actual deleted constants. The original README
reports 4063 dropped constants, a discrepancy of one not resolved here.

Fixed experiment baseline: 91b273530883b723ef4422436e0dc3557749325a.
Upstream main checked during this round: 98d36aafeeb30c1f40fdda96c3574faa34dfa413.
Lean v4.37.0-rc1, Mathlib 31ce06eaadf4a200c0e1407c5f10953cf606b8f8.
Kernel/Comparator/build metrics remain unmeasured. No Lean proof edited.

Future work: replace associations with actual independently checked
occurrence-level rewrite certificates, nonuniform costs and conflicts, then
measure reachability on the rewritten kernel graph. Do not treat historical
candidates as unclaimed or submit them without checking current upstream.
