
namespace ProofOpt.ScopedFixtures
theorem a (p q r s : True) : True ∧ True := And.intro p q
theorem b (p q r s : True) : True ∧ True := And.intro r s
theorem depA (n m : Nat) (p : n = n) (q : m = m) :
    (n = n) ∧ (n = n) := And.intro p p
theorem depB (n m : Nat) (p : n = n) (q : m = m) :
    (m = m) ∧ (m = m) := And.intro q q
theorem equalA (p : True) : True ∧ True := And.intro p p
theorem equalB (q : True) : True ∧ True := And.intro q q
theorem mismatch (n : Nat) : True := True.intro
end ProofOpt.ScopedFixtures
#proofopt_extract_exact 0 "ProofOpt.ScopedFixtures.a" "ProofOpt.ScopedFixtures.b"
#proofopt_extract_exact 1 "ProofOpt.ScopedFixtures.depA" "ProofOpt.ScopedFixtures.depB"
#proofopt_extract_exact 2 "ProofOpt.ScopedFixtures.equalA" "ProofOpt.ScopedFixtures.equalB"
#proofopt_extract_exact 3 "ProofOpt.ScopedFixtures.a" "ProofOpt.ScopedFixtures.mismatch"
#proofopt_extract_exact 4 "ProofOpt.ScopedFixtures.a" "ProofOpt.ScopedFixtures.a"
#proofopt_extract 5 "ProofOpt.ScopedFixtures.a" "ProofOpt.ScopedFixtures.b"
