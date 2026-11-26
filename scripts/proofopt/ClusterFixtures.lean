
namespace ProofOpt.ClusterFixtures
theorem a (p q r s : True) : True ∧ True := And.intro p q
theorem b (p q r s : True) : True ∧ True := And.intro r s
theorem c (p q r s : True) : True ∧ True := And.intro q r
theorem depA (n m k : Nat) (p : n = n) (q : m = m) (r : k = k) :
    (n = n) ∧ (n = n) := And.intro p p
theorem depB (n m k : Nat) (p : n = n) (q : m = m) (r : k = k) :
    (m = m) ∧ (m = m) := And.intro q q
theorem depC (n m k : Nat) (p : n = n) (q : m = m) (r : k = k) :
    (k = k) ∧ (k = k) := And.intro r r
theorem sameA (n : Nat) (p : n = n) (q : True) : (n = n) ∧ (n = n) := And.intro p p
theorem sameB (n : Nat) (p : n = n) (q : True) : (n = n) ∧ (n = n) := And.intro p p
theorem sameC (n : Nat) (p : n = n) (q : True) : (n = n) ∧ (n = n) := And.intro p p
theorem mismatch (n : Nat) : True := True.intro
end ProofOpt.ClusterFixtures
#proofopt_cluster_exact 0 "ProofOpt.ClusterFixtures.a" "ProofOpt.ClusterFixtures.b" "ProofOpt.ClusterFixtures.c"
#proofopt_cluster_exact 1 "ProofOpt.ClusterFixtures.depA" "ProofOpt.ClusterFixtures.depB" "ProofOpt.ClusterFixtures.depC"
#proofopt_cluster_exact 2 "ProofOpt.ClusterFixtures.sameA" "ProofOpt.ClusterFixtures.sameB" "ProofOpt.ClusterFixtures.sameC"
#proofopt_cluster_exact 3 "ProofOpt.ClusterFixtures.a" "ProofOpt.ClusterFixtures.b" "ProofOpt.ClusterFixtures.mismatch"
#proofopt_cluster_exact 4 "ProofOpt.ClusterFixtures.a" "ProofOpt.ClusterFixtures.b" "ProofOpt.ClusterFixtures.a"
#proofopt_cluster 5 "ProofOpt.ClusterFixtures.a" "ProofOpt.ClusterFixtures.b" "ProofOpt.ClusterFixtures.c"
