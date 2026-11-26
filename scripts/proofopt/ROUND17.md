# Round 17: first concrete shared-lemma source refactor

Prior CI is now observable via the branch-filtered Actions REST endpoint. Round 14 and 15 failed in KernelDag typechecking; round 16 failed in TypedExtract parsing (historical jobs skipped). Repair the diagnosed errors and independently exercise the repaired tools before relying on them.

Move the duplicated Hermitian sign-matrix lemma to the existing definition module, remove the two child declarations and explicitly retarget their local uses. Do not add aliases, imports, or simp attributes. Current upstream still contains both duplicates at de458307ca8942be9820466417994828a369cbce. This branch is based on the historical readable snapshot, not the current upstream or original flagship baseline. Any qualification or import regression must be caught by the full build; the source change alone is not a certificate.

The expected gain is one declaration only if both old lemmas were reachable; actual gains must come from two independent exported graphs. The comparison reports per-root and union removed/added declarations, includes the new shared lemma, refuses scope/ownership drift and rejects nonpositive union gain. This does not measure expression DAG or full CPU savings. The build log is a diagnostic, not a matched timing experiment. No independent Comparator/Nanoda result is claimed.

Tests:
- `node scripts/proofopt/compare_refactor.cjs --self-test`
- `lean scripts/proofopt/KernelDag.lean`
- `lean --run scripts/proofopt/KernelDag.lean --self-test`
- concatenate TypedExtract.lean and TypedFixtures.lean and run Lean on the result.
- See round 17 workflow for historical artifact verification, rebuild and full graph export.

The tooling is Fork-only; upstream README asks not to submit extraneous tools. A future upstream contribution would contain only a validated, rebased source patch and must be separately approved.
