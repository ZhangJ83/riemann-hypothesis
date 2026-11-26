# Round 16: typed certificate sandbox

This pass re-reads theorem types and values from Lean's environment. It
does not deserialize printed universe expressions or trust round 15's
syntax-only report. It identifies ordered closed mismatch pairs, builds
a common term and binds holes in an order whose inferred types can be
reconstructed from previous pairs. It rejects open mismatches, whole
proof holes, incompatible universe parameter lists and unresolved types.

Certification attempts three theorem declarations (a generalized shared
lemma and two applications with exactly the original statement types).
Kernel checking is explicitly enabled and asynchronous elaboration is
disabled. The axiom audit allows only the three standard axioms from the
project's README. The environment is restored after each probe. Even a
successful certificate is not a proof rewrite: source visibility,
transitive replacement cycles and global closure/DAG profitability are
still required.

## Reproduce

    node scripts/proofopt/typed_driver.cjs --self-test
    cat scripts/proofopt/TypedExtract.lean scripts/proofopt/TypedFixtures.lean > /tmp/TypedTest.lean
    lean /tmp/TypedTest.lean
    node scripts/proofopt/typed_driver.cjs scripts/proofopt/typed_historical_pairs.json scripts/proofopt/TypedExtract.lean /tmp/Real.lean /tmp/pairs.json
    lake env lean /tmp/Real.lean

The historical file carries three round-12 reference-signature hypotheses.
They are a separate integration input, not proven AU candidates. The
driver also accepts a round-15 report (schema 1). It restricts names to
a conservative ASCII subset, deduplicates unordered pairs and reports
omissions. It does not silently treat a rejected certificate as a saving.

No actual Lean run or global optimization result was obtained locally.
Only the driver function assertions were executed in the JS isolate.
The workflow separates quick standalone Lean fixtures from the expensive
historical integration. The original flagship baseline remains unchanged.
