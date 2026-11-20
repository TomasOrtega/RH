import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Replace the relevant objects with their definitions. Simplify by unfolding definitions. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Proceed by induction.

Treat this case separately. Treat this case separately. Proceed by induction. Treat this case separately. Treat this case separately.

Treat this case separately. Treat this case separately. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the claim to the hypotheses of an applicable result.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Proceed by induction.

Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules. Establish an intermediate fact. Chain the equalities or inequalities of the calculation.

Simplify using the standard rewrite rules. Treat this case separately. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.crystallineComparison.annExt_of :
    DinvExt → AnnExt := by
  intro h F G B _ _ _ _ σ ψ L _ _ V _ _ ρ
  have hD := h F G B σ L V ρ
  have hinj : Function.Injective ((Dinv σ ρ).subtype.baseChange L) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (Dinv σ ρ).injective_subtype
  refine ⟨fun e hadm => ?_, fun q n T hA x hx => ?_⟩
  · unfold admitted at hadm ⊢
    rw [← LinearEquiv.finrank_map_eq (AlgebraTensorModule.assoc F F L L V B), hD, Module.finrank_baseChange]
    rw [← hadm]
    change Module.finrank L (LinearMap.range ((Dinv σ ρ).subtype.baseChange L)) = _
    rw [LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]
  · unfold AnnD at hA
    dsimp only
    have comm : ∀ (f : V →ₗ[F] V) (g : B →ₗ[F] B) (y : (L ⊗[F] V) ⊗[F] B),
        AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (f.baseChange L) g y) =
          (AlgebraTensorModule.map f g).lTensor L (AlgebraTensorModule.assoc F F L L V B y) := by
      intro f g y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul u b =>
        induction u using TensorProduct.induction_on with
        | zero => simp
        | tmul a v => simp
        | add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]
      | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
    have hmem : AlgebraTensorModule.assoc F F L L V B x ∈ (Dinv σ ρ).baseChange L := by
      rw [← hD]
      exact Submodule.mem_map_of_mem hx
    apply (AlgebraTensorModule.assoc F F L L V B).injective
    rw [map_sum, map_zero]
    simp only [map_zsmul, comm]
    obtain ⟨z, hz⟩ := Submodule.toBaseChange_surjective' L (Dinv σ ρ) hmem
    rw [← hz]
    clear hz hmem
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a w =>
      simp only [Submodule.coe_toBaseChange_tmul, LinearMap.lTensor_tmul]
      have := hA w w.2
      calc _ = TensorProduct.mk F L (V ⊗[F] B) a (∑ j ∈ Finset.range (n + 1), ((-1) ^ j * (q : ℤ) ^ j.choose 2) • (AlgebraTensorModule.map (T j) (ψ ^ (n - j))) w) := by
            simp only [map_sum, map_zsmul, TensorProduct.mk_apply]
        _ = 0 := by rw [this, map_zero]
    | add z₁ z₂ h₁ h₂ => simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, smul_add, h₁, h₂, add_zero]
