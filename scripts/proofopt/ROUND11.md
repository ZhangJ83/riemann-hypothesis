# Round 11: full reference-graph cut census

The round-10 runner completed successfully. Download the artifact at
https://github.com/ZhangJ83/riemann-hypothesis/actions/runs/45748541486/artifacts/15085425261
before its expiry. Verify ZIP SHA-256 54df87dd4ecc9f1fcfb243f4bd4e5666b983e1516105082b9114553e6b5063ee.
Unzip it; use the provided modules.txt and kernel-graph.jsonl.gz.

## Reproduce

Install Python 3 and numpy/scipy (optional orjson acceleration). From scripts/proofopt:

    OPENBLAS_NUM_THREADS=1 python -m unittest -v test_graph_cut
    OPENBLAS_NUM_THREADS=1 /usr/bin/time -v python graph_cut.py \
      /path/to/kernel-graph.jsonl.gz /path/to/modules.txt \
      5a1f971e33e3c0449137327e7ed46ae4d8742c31e4c0e8449525005d03c5591c report.json

The output records the whole graph census, each root, and the top 20 exact single-cut
bounds checked by a separate reachability traversal. baseline_round11.json
records the observed results and the input artifact identity. It omits the lost-name
samples printed by the CLI.

## Model

Construct a graph with an extra super-root pointing to all five target declarations.
For each reachable internal theorem other than a protected root, redirect only
its value-only edges through a unique gate. Type and kernel metadata edges remain
unchanged, even if also found in the proof value. Removing the gate removes all
value-only edges of that theorem. A reachable declaration is disconnected iff
every super-root path to it passes through the gate, i.e. iff the gate dominates it.
A weighted dominator subtree counts these declarations exactly. All candidate
bounds are computed simultaneously, not by separate full searches. The direct
reachability checks verify the top 20. The randomized test checks every candidate
against direct traversal in 200 graphs, including cycles and external references.

The cut is a relaxation, not a theorem replacement. Any single replacement that
preserves type/metadata cannot eliminate more old reachable declarations than
this cut in this graph, since the new proof can add edges but cannot remove the
retained edges. Bounds for different gates may overlap. In particular the
DenominatorBound chain illustrates why they cannot be summed. The largest bounds
belong to main mathematical bottlenecks, not proven redundancy.

## Limitations

This is an exploratory reference graph from cached imported Lean environment, not
a full expression export and not a fresh independent kernel check. The exporter
does not establish completeness of all implicit kernel dependencies. The graph
contains no expression DAG, type equality certificates, or proof replacement
terms. No source proofs were changed this round. The 49,508 figure applies to
the separately pinned readable version, not the original experimental baseline.
The cached lake build CPU time is not a full-build benchmark. Do not credit any
of these bounds or the upstream migration as flagship compression.
