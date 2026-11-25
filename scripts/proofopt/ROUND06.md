# ProofOpt Round 06: disk-backed kernel export metrics

## What changed
A second implementation of the Round 04 structural-v1 measurement pipeline uses SQLite for raw-index translation, exact canonical-key interning, expression adjacency, declarations, ownership, and recursive SQL reachability. It processes NDJSON line-by-line rather than retaining the input and entire graph as JavaScript objects. A shared database makes structural IDs comparable across snapshots. SQL UNION deduplicates graph vertices, including cyclic declaration-metadata references. Input hashes and owner coverage checks remain explicit. No Lean source or protected challenge file was changed in this round.

## Reproduce
From scripts/proofopt:

```sh
python3 -m unittest -v test_disk_metrics
python3 disk_metrics.py nat.db measure nat_prefix.ndjson - --roots Nat Nat.rec
python3 -c "from pathlib import Path; from test_disk_metrics import fixture; fixture(Path('stress.ndjson'),500000)"
/usr/bin/time -v python3 disk_metrics.py stress.db measure stress.ndjson - --roots root
```

For a real before/after capture, with a **new** database:
```sh
python3 disk_metrics.py comparison.db compare before/solution.ndjson before/ownership.ndjson after/solution.ndjson after/ownership.ndjson --roots riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive
```

Use SQLite >= 3.34 (compound recursive CTE support). The benchmark generator deliberately creates synthetic syntax, not type-correct Lean. Input generation is separate from the timed process. In the recorded benchmark the larger fixture was generated with streaming writes, using the same records as the test helper. Outputs are in baseline_round06.json. A new database is required by the CLI; failed or interrupted ingests can leave a database file. Do not reuse it as a successful capture.

## Real fixture provenance
nat_prefix.ndjson is the first 51 records of leanprover/lean4export's examples/Nat.add_succ.ndjson, pinned at df81913eee5519d5a88ae5b0fd701b5298cc29ab. The exporter repository license is copied in LICENSE-lean4export. This is an excerpt, not the complete Nat.add_succ proof. The original Round 04 JavaScript analyzer independently returned the same counts for Nat and Nat.rec.

## Limits
This is a prototype structural metric, not a Lean kernel verifier. The SQL temporary storage setting and bounded page cache reduce reliance on in-process graph structures but do not guarantee a fixed RAM ceiling. SQL deduplication, indexes and rollback journals require disk space; no 60 GB export has been tested. The benchmark is a deep linear synthetic DAG, not a realistic branching workload. Full exporter-variant parity, arbitrary declaration-name handling, schema evolution, robust crash recovery, large-scale transaction tuning, independent Lean verification and true project measurements remain necessary. Do not mix backends for headline metrics until parity is established on identical real inputs. The existing JavaScript tool remains available for cross-checks. The Round 05 proof changes remain uncompiled.
