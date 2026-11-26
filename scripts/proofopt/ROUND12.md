# Round 12: first cross-module consolidation and source budget

The readable baseline remains 2746005d8130ee6d0c82d771ec11d69521a65093; the original
flagship baseline remains 91b273530883b723ef4422436e0dc3557749325a.
Round 11's explicit-reference graph suggests three cross-module theorem pairs
with identical reference signatures. Source inspection confirms duplicate
statements/proofs, but only the actual Lean build can certify this candidate.

* Move the Hermitian sign-matrix lemma to its defining module, replace all five
  observed caller declarations across Fock, Localization, and NegativeIndices.
* Reuse New.mem_valRingCp in the torsion-value proof.
* Reuse the existing FrameTheorem result in ExponentLattices.

No new imports or dependency pins. Four names removed, one name added in source.
All six changed mathematical files are explicitly allowlisted. Challenge,
comparator, final statements and toolchain are unchanged. The reference census
cannot guarantee every source-level use is captured, so build failure is a
possible result. No proven dependency, expression-DAG or CPU savings yet.

The 2,000-line goal covers ALL tracked project-owned Lean sources in src, not just
Main or files called directly by the final theorems. Nonblank lines include
comments; also report physical lines, bytes, and conservative 100-codepoint
wrapped nonblank count (both nonblank and wrapped must be at most 2,000).
Keep external dependencies fixed; no hiding new proof material in generated
artifacts, packages or tactics. If necessary, count any proof-generating code
outside src as additional cost and reject hidden imports. This is a proposed
operational scope, not a mathematical theorem about possible compression.

CI: run the snapshot audit with round12_plan.json, source-budget tests and
whole-project measurement, restore the pinned baseline cache, rebuild the
candidate, check axioms and extract its reference graph. A cache-assisted build
is not an independent comparator/kernel replay. The original large baseline
remains unmeasured. This research branch is not an upstream PR.
