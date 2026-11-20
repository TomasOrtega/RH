import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

/- English proof (translation)
Introduce a local definition for the expression. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Supply the required witnesses or components. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components.

Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the indicated hypotheses using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem adjoin_alg {V : Type} [AddCommGroup V] [Module ℂ V] {R : Type} [CommRing R] [Algebra ℂ R]
    (φ : R →ₐ[ℂ] Module.End ℂ V) (S : Submodule ℂ V) (t : Set R) (ht : ∀ r ∈ t, AlgMod S ⊥ (φ r)) :
    ∀ r ∈ Algebra.adjoin ℂ t, AlgMod S ⊥ (φ r) := by
  let I : Ideal R :=
    { carrier := {r | ∀ x ∈ S, φ r x = 0}
      add_mem' := fun {a b} ha hb x hx => by
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [map_add, LinearMap.add_apply, ha x hx, hb x hx, add_zero]
      zero_mem' := fun x _ => by simp
      smul_mem' := fun c r hr x hx => by
        simp only [Set.mem_setOf_eq] at hr ⊢
        rw [smul_eq_mul, map_mul, Module.End.mul_apply, hr x hx, map_zero] }
  have hint : ∀ r ∈ t, IsIntegral ℂ (Ideal.Quotient.mkₐ ℂ I r) := by
    intro r hr
    obtain ⟨p, hp, hx⟩ := ht r hr
    refine ⟨p, hp, ?_⟩
    rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem]
    intro x hxS
    have hx' := hx x hxS
    rw [Polynomial.aeval_algHom_apply, Submodule.mem_bot] at hx'
    exact hx'
  intro r hr
  have h1 : Ideal.Quotient.mkₐ ℂ I r ∈ Algebra.adjoin ℂ (Ideal.Quotient.mkₐ ℂ I '' t) := by
    rw [Algebra.adjoin_image]
    exact ⟨r, hr, rfl⟩
  have h2 : Ideal.Quotient.mkₐ ℂ I r ∈ integralClosure ℂ (R ⧸ I) := by
    refine Algebra.adjoin_le ?_ h1
    rintro _ ⟨r', hr', rfl⟩
    exact hint r' hr'
  obtain ⟨p, hp, hev⟩ := h2
  refine ⟨p, hp, fun x hx => ?_⟩
  rw [← Polynomial.aeval_def, Polynomial.aeval_algHom_apply, Ideal.Quotient.mkₐ_eq_mk,
    Ideal.Quotient.eq_zero_iff_mem] at hev
  rw [Polynomial.aeval_algHom_apply, Submodule.mem_bot]
  exact hev x hx

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Check the elementary cases of the proposition.

A detailed English derivation is pending.
-/
theorem UpperTheory.algMod_bot_of_mem_adjoin_commuting :
    ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) (s : Set (Module.End ℂ M)), (∀ x ∈ s, ∀ y ∈ s, x * y = y * x) → (∀ T ∈ s, AlgMod S ⊥ T) → ∀ T ∈ Algebra.adjoin ℂ s, AlgMod S ⊥ T := by
  intro M _ _ S s hcomm hs T hT
  letI : CommRing (Algebra.adjoin ℂ s) := Algebra.adjoinCommRingOfComm ℂ hcomm
  have hmem : (⟨T, hT⟩ : Algebra.adjoin ℂ s) ∈
      Algebra.adjoin ℂ (((↑) : Algebra.adjoin ℂ s → Module.End ℂ M) ⁻¹' s) := by
    rw [Algebra.adjoin_adjoin_coe_preimage]
    trivial
  exact adjoin_alg (Algebra.adjoin ℂ s).val S _ (fun r hr => hs r hr) _ hmem
