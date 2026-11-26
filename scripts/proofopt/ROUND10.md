# Round 10: readable upstream integration baseline

The upstream README explicitly records the 2026-11-25 transition to a condensed readable edition. The original benchmark 91b273530883b723ef4422436e0dc3557749325a remains immutable; the older upstream line is now alpoge. New integration base 2746005d8130ee6d0c82d771ec11d69521a65093 has a different layout and TauCeti package. Never compare old vs new as an optimizer result.

This branch intentionally contains no mathematical change. It establishes a fail-closed source/ownership snapshot and a fork-only cached compilation and exploratory declaration-extraction workflow. The snapshot enumerates exact tracked src modules, excluding Mathlib and TauCeti from project ownership. It protects the new root Challenge.lean, comparator settings, Main, Statements and dependency pins. The workflow refuses missing cache rather than automatically attempting a full clean build. Its build cannot certify the old round-05 candidate; that branch remains untouched.

Run the local snapshot checks on a clone of this branch:
```sh
node scripts/proofopt/test_snapshot.mjs
mkdir -p /tmp/proofopt-round10
node scripts/proofopt/snapshot_cli.mjs 2746005d8130ee6d0c82d771ec11d69521a65093 /tmp/proofopt-round10
```

The baseline snapshot tests and metadata were produced from the actual GitHub tree. The inherited KernelGraph.lean is exploratory and not yet Lean-compiled in this environment; it is not a complete structural-v1 DAG measurement and its implicit kernel dependencies require audit. The CI job uses read-only permissions, public caches, and a bounded graph artifact. It never publishes cache or creates a PR. If Actions is disabled in the fork or the connector cannot update workflow files, run the equivalent commands on a suitable Linux host. The new baseline is only a contribution integration track, not a redefinition of the original 20/20/30 benchmark.
