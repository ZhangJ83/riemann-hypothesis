
namespace ProofOptAliasFixture
theorem A (n : Nat) : n = n := rfl
theorem B (m : Nat) : m = m := rfl
theorem C : True := True.intro
theorem P.{u} (α : Type u) (a : α) : a = a := rfl
theorem Q.{v} (β : Type v) (b : β) : b = b := rfl
end ProofOptAliasFixture
#proofopt_alias 0 "ProofOptAliasFixture.A" "ProofOptAliasFixture.B"
#proofopt_alias 1 "ProofOptAliasFixture.P" "ProofOptAliasFixture.Q"
#proofopt_alias 2 "ProofOptAliasFixture.A" "ProofOptAliasFixture.C"
#proofopt_alias 3 "ProofOptAliasFixture.A" "Nat"
#proofopt_alias 4 "ProofOptAliasFixture.A" "ProofOptAliasFixture.A"
#proofopt_alias 5 "ProofOptAliasFixture.A" "ProofOptAliasFixture.Missing"
