# Round 19: proof-value shortcut superoptimizer

Round 18 ranked the impossible empty-value cut. This pass introduces an actual candidate replacement expression: an existing theorem constant. It searches reachable project theorem values for direct theorem references and two-hop theorem-value paths through editable project theorems. Equal sets of type references and a conservative public-name filter are search heuristics, not Lean type equality. The candidate's witness path, module, cut bound, exact modeled net gain and independent traversal check are recorded.

## Exact graph accounting

For a private value gate G, its dominator subtree D is exactly the set lost by deleting G's outgoing value edges. Replace G's outgoing edges with the single edge to candidate T. If T is outside D, the cut loss is unchanged. If T is inside D, only the vertices reachable from T inside D with G's old outgoing edges removed are rescued. Any path from outside D into D in the cut graph would contradict its definition. Subtract the rescued weight for the exact single-site net loss. Independently replay shortlisted candidates on the full graph.

Every shortcut follows an original path, so each root's new reachable set is a subset of its old set, even with multiple shortcuts. Reject targets that can reach their owners in the original graph, including through kernel edges; bounded checks fail closed. Joint selection recomputes closure, accepting strict positive marginal improvement instead of summing single-site scores. Protected final roots cannot be sources or targets. Type/kernel edges are unchanged. This is a bounded greedy search: zero-cut sites, longer paths, more general substitutions, and candidates filtered by name or type-reference signature are not covered.

## Semantic layer

AliasCertificate.lean constructs a fresh theorem with the unchanged source type and level parameters, whose value is the existing replacement constant applied to corresponding universe parameters. The Lean kernel must accept addDecl and the axiom whitelist must pass. The environment is restored after each test. The machine-readable parser requires exactly one outcome per candidate; replay checks graph and scope digests and recomputes the deterministic candidate list before joint scoring successful certificates only. The result remains a sandbox certificate and counterfactual, not a source rewrite or proof of import visibility.

## Reproduce

- node scripts/proofopt/alias_pass.cjs --self-test
- node scripts/proofopt/alias_pass.cjs GRAPH.gz SHA256 SCOPE_DIR report.json
- node scripts/proofopt/alias_pass.cjs --render report.json scripts/proofopt/AliasCertificate.lean Real.lean
- lake env lean Real.lean > real.log 2>&1
- node scripts/proofopt/alias_pass.cjs --parse report.json real.log certificates.json
- node scripts/proofopt/alias_pass.cjs --replay GRAPH.gz SHA256 SCOPE_DIR certified-joint.json certificates.json

The fork-only workflow tests six Lean fixtures, mines the full historical graph, attempts certificates, and recomputes joint gains. The round 18 parent contains three modified Lean source files compared with the historical baseline, so certification builds a detached exact historical worktree, not the modified parent. No new project source or protected files are changed in this commit. The historical graph is not the locked original flagship baseline; all actual compression and originality metrics remain unmeasured. Do not ship the fork-only optimizer/CI in an upstream proof-source PR.
