
namespace ProofOpt.ExtractFixtures
theorem p : True := True.intro
theorem q : True := True.intro
theorem r : True := True.intro
theorem a : True ∧ True := And.intro p p
theorem b : True ∧ True := And.intro q q
theorem c : True ∧ True := And.intro q r
theorem d : True ∧ True := And.intro p q
theorem e : True := p
end ProofOpt.ExtractFixtures
#proofopt_extract 0 "ProofOpt.ExtractFixtures.a" "ProofOpt.ExtractFixtures.b"
#proofopt_extract 1 "ProofOpt.ExtractFixtures.a" "ProofOpt.ExtractFixtures.a"
#proofopt_extract 2 "ProofOpt.ExtractFixtures.a" "ProofOpt.ExtractFixtures.e"
