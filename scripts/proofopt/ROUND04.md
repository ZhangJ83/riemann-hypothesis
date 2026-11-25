# Round 04 — export-based measurement and structural regression gates

The prior graph engine can rank hypothetical dependency rewrites but cannot supply trustworthy
expression sizes from source text. This package reads the upstream `leanexport` NDJSON directly,
without elaborating or trusting source-name guesses. The official format specification is
[here](https://github.com/leanprover/lean4export/blob/df81913eee5519d5a88ae5b0fd701b5298cc29ab/format_ndjson.md).
Support for 3.0 is for the older published sample; 3.1 uses the documented declaration shape.

## Fixed metric (structural-v1)

Intern each expression by constructor, already-interned child IDs, typed constant name and
structural universe levels. Ignore bound-variable display names, metadata wrappers and the let
nondep hint; preserve binderInfo, literal values, de Bruijn indices, constant identity, projection
index and universe parameter names. Count distinct interned Expr nodes, not references or levels.
No beta/delta reduction or proof-irrelevance normalization is done. Traverse types, declaration
values and recursor rule RHSs; retain mutual groups, constructor/inductive metadata, quotient
package and literal support. This is a conservative export-reference closure, not an exact
minimal proof dependency count. Publish type/value/combined counts for each root and union.
Project-only counts use an explicit ownership sidecar; unresolved reachable names fail, and
absence of the sidecar produces null rather than zero. No source-name prefix classification.

The comparison requires equal Lean and exporter identity; compares root type syntax in one
structural interner, checks ownership drift and per-root and union axiom growth. It rejects
unexpected axioms including sorryAx and unsafe reachable declarations. This is a *necessary*
structural preflight, not semantic equivalence: changes to definitions referenced by an unchanged
root type must still be caught by Comparator, and the export must be independently checked.
The type syntax guard deliberately rejects some definitionally equivalent types. The graph
adapter emits existing Round 03 schema with typed name keys and explicit ownership. The export is
root-targeted, so alternatives outside the exported closure require an expanded export.

## Capture and run

Use a separate checkout of the fixed baseline or candidate; first obtain the appropriate cache
per upstream README. Do not use cached artifacts to claim a clean proof verification.
Run the capture script from inside that checkout:

    bash /path/to/proofopt/capture_export.sh /absolute/path/to/capture
    node scripts/proofopt/export_metrics_cli.mjs measure capture/solution.ndjson capture/ownership.ndjson > metrics.json
    node scripts/proofopt/export_metrics_cli.mjs compare before/solution.ndjson before/ownership.ndjson after/solution.ndjson after/ownership.ndjson > comparison.json

Check capture.json commit, Lean, Mathlib, and input SHA-256 values against comparison.json.
Keep identical pinned toolchain/Mathlib and capture strategy. CPU costs require a separate
clean benchmark. Node CLI and Lean capture/ownership producer were NOT executed this round.
The owner producer uses the previous uncompiled Environment APIs, so compilation and complete
private-declaration coverage remain a blocker. Large full-repository memory use is unmeasured.

## Tests

    node scripts/proofopt/test_export_metrics.mjs
    # Obtain the public fixture (do not edit it):
    curl -L https://raw.githubusercontent.com/leanprover/lean4export/df81913eee5519d5a88ae5b0fd701b5298cc29ab/examples/Nat.add_succ.ndjson -o Nat.add_succ.ndjson
    node scripts/proofopt/test_export_metrics.mjs Nat.add_succ.ndjson

The exact library/test functions were executed in V8, including the actual fixture retrieved
through GitHub, and independently traversed its raw indices. The migrated 3.1 fixture is synthetic,
not a native 3.1 export. The synthetic tests are graph/format tests, NOT valid Lean proofs.
No changes under src or upstream PR. This package remains on the research Fork.

## Remaining gates

* Obtain a real full Main export and lossless ownership manifest from a compiled pinned checkout.
* Verify against independent kernel/Comparator/Nanoda and validate the normalized metric at scale.
* Lock original measured counts before evaluating actual mathematical proof patches.
* Full build CPU metric, two-project generalization and originality review remain open.
