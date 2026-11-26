
namespace ParamFixture
theorem generic (a : Nat) : a = a := rfl
theorem specialized : 7 = 7 := rfl
theorem poly.{u} (α : Type u) (a : α) : a = a := rfl
theorem reordered (p q : Prop) (hq : q) (hp : p) : p ∧ q := ⟨hp, hq⟩
theorem original (p q : Prop) (hp : p) (hq : q) : p ∧ q := ⟨hp, hq⟩
theorem missing (p q : Prop) (hp : p) : p ∧ q → p := fun _ => hp
theorem needs (p q : Prop) (hp : p) : q → p ∧ q := fun hq => ⟨hp, hq⟩
theorem wrong : True := True.intro
theorem depends (α : Type) (x : α) (P : α → Prop) (h : P x) : P x := h
theorem dependsReorder (α : Type) (P : α → Prop) (x : α) (h : P x) : P x := h
axiom forbidden : False
theorem forbiddenProof : False := forbidden
theorem forbiddenOwner : False → False := fun h => h
end ParamFixture
#proofopt_param 0 "ParamFixture.specialized" "ParamFixture.generic"
#proofopt_param 1 "ParamFixture.generic" "ParamFixture.poly"
#proofopt_param 2 "ParamFixture.original" "ParamFixture.reordered"
#proofopt_param 3 "ParamFixture.dependsReorder" "ParamFixture.depends"
#proofopt_param 4 "ParamFixture.specialized" "ParamFixture.wrong"
#proofopt_param 5 "ParamFixture.original" "ParamFixture.original"
#proofopt_param 6 "ParamFixture.original" "ParamFixture.absent"
#proofopt_param 7 "ParamFixture.forbiddenOwner" "ParamFixture.forbiddenProof"
#proofopt_param 8 "ParamFixture.missing" "ParamFixture.needs"
