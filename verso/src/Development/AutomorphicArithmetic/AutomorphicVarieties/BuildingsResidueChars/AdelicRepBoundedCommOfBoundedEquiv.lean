import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

/- English proof (translation)
Introduce `hEq hSub hOver G _ Γ Λ hc hΛ`. Take `⟨h1, h2⟩` from `hc`. Establish `f1 : (Γ.subgroupOf Λ).FiniteIndex` using `⟨h1⟩`. Establish `f2 : (Λ.subgroupOf Γ).FiniteIndex` using `⟨h2⟩`. Establish `b1` using `hSub Λ (Γ.subgroupOf Λ) f1 hΛ`.

Establish `e : (Γ.subgroupOf Λ) ≃* (Λ.subgroupOf Γ)` using `{ toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩ invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl map_mul' := fun _ _ => rfl }`. Establish `b2` using `hEq _ _ ⟨e⟩ b1`. Conclude with `hOver Γ (Λ.subgroupOf Γ) f2 b2`.
-/
theorem UpperTheory.adelic_rep_bounded_comm_of_bounded_equiv :
    UpperTheory.V.Af.CohB.BddEquiv → UpperTheory.V.Af.BA.BddSub → UpperTheory.V.Af.BA.BddOver → UpperTheory.V.Af.BA.BddComm := by
  intro hEq hSub hOver G _ Γ Λ hc hΛ
  obtain ⟨h1, h2⟩ := hc
  have f1 : (Γ.subgroupOf Λ).FiniteIndex := ⟨h1⟩
  have f2 : (Λ.subgroupOf Γ).FiniteIndex := ⟨h2⟩
  have b1 := hSub Λ (Γ.subgroupOf Λ) f1 hΛ
  have e : (Γ.subgroupOf Λ) ≃* (Λ.subgroupOf Γ) :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl }
  have b2 := hEq _ _ ⟨e⟩ b1
  exact hOver Γ (Λ.subgroupOf Γ) f2 b2
