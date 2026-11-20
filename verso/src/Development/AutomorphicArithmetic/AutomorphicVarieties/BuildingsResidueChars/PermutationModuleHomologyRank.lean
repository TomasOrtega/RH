import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup

open CategoryTheory UpperTheory.V.Af.BA in
/- English proof (translation)
Introduce `Γ X _ _ h`. Take `⟨R, hR, hRx⟩` from `h`. Use `haveI := hR.fintype`. Use `⟨Fintype.card R, fun A => ?_⟩` and prove the remaining obligations. Set `Φ : (PC Γ X ⟶ A) →ₗ[ℂ] (R → A)` to `{ toFun := fun φ r => φ.hom (Finsupp.single (r : X) 1) map_add' := fun φ ψ => by`.

Use extensionality with `r`. Both sides reduce to the same expression. Use the proof step `map_smul' := fun c φ => by`. Use extensionality with `r`. Use `rfl }`.

Establish `key : ∀ (χ : PC Γ X ⟶ A) (g : Γ) (x : X), χ.hom (Finsupp.single x 1) = A.ρ g⁻¹ (χ.hom (Finsupp.single (g • x) 1))`. Introduce `χ g x`. Rewrite using `[← Rep.hom_comm_apply]`. Use `congr 1`. Use `show _ = permC Γ X g⁻¹ (Finsupp.single (g • x) 1)`.

Rewrite using `[permC_single, inv_smul_smul]`. Establish `hinj : Function.Injective Φ`. Introduce `φ ψ hφψ`. Apply `PC_ext` to reduce the goal to its premises. Introduce `x`.

Take `⟨g, hg⟩` from `hRx x`. Establish `h1` using `congrFun hφψ ⟨g • x, hg⟩`. Rewrite using `[key φ g x, key ψ g x]`. Conclude with `congrArg _ h1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem UpperTheory.permutation_module_homology_rank :
    UpperTheory.V.Af.BA.RankHomPerm := by
  intro Γ X _ _ h
  obtain ⟨R, hR, hRx⟩ := h
  haveI := hR.fintype
  refine ⟨Fintype.card R, fun A => ?_⟩
  let Φ : (PC Γ X ⟶ A) →ₗ[ℂ] (R → A) :=
    { toFun := fun φ r => φ.hom (Finsupp.single (r : X) 1)
      map_add' := fun φ ψ => by
        ext r
        rfl
      map_smul' := fun c φ => by
        ext r
        rfl }
  have key : ∀ (χ : PC Γ X ⟶ A) (g : Γ) (x : X),
      χ.hom (Finsupp.single x 1) = A.ρ g⁻¹ (χ.hom (Finsupp.single (g • x) 1)) := by
    intro χ g x
    rw [← Rep.hom_comm_apply]
    congr 1
    show _ = permC Γ X g⁻¹ (Finsupp.single (g • x) 1)
    rw [permC_single, inv_smul_smul]
  have hinj : Function.Injective Φ := by
    intro φ ψ hφψ
    apply PC_ext
    intro x
    obtain ⟨g, hg⟩ := hRx x
    have h1 := congrFun hφψ ⟨g • x, hg⟩
    rw [key φ g x, key ψ g x]
    exact congrArg _ h1
  calc Module.rank ℂ (PC Γ X ⟶ A) ≤ Module.rank ℂ (R → A) := Φ.rank_le_of_injective hinj
    _ = _ := by rw [rank_fun_eq_lift_mul, Cardinal.lift_id]
