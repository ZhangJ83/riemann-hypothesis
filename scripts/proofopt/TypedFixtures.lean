
namespace ProofOptFixtures
theorem one : (1 : Nat) = 1 := @Eq.refl Nat 1
theorem two : (2 : Nat) = 2 := @Eq.refl Nat 2
theorem oneCopy : (1 : Nat) = 1 := @Eq.refl Nat 1
theorem boolTrue : true = true := @Eq.refl Bool true
theorem openLeft (x y : Nat) : x = x := @Eq.refl Nat x
theorem openRight (x y : Nat) : y = y := @Eq.refl Nat y
theorem plainTrue : True := True.intro
end ProofOptFixtures

#proofopt_expect "ProofOptFixtures.one" "ProofOptFixtures.two" 1
#proofopt_expect "ProofOptFixtures.one" "ProofOptFixtures.oneCopy" 0
#proofopt_expect "ProofOptFixtures.one" "ProofOptFixtures.boolTrue" 2
#proofopt_reject "ProofOptFixtures.openLeft" "ProofOptFixtures.openRight"
#proofopt_reject "ProofOptFixtures.one" "ProofOptFixtures.plainTrue"
#proofopt_reject "ProofOptFixtures.one" "ProofOptFixtures.one"
#proofopt_reject "ProofOptFixtures.one" "ProofOptFixtures.notFound"
