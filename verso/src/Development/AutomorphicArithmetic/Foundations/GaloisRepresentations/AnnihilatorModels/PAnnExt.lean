import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DinvExact

open TensorProduct Module
open UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `h F G B _ _ _ _ σ ψ L _ _ V _ _ ρ`. Establish `hD` using `h F G B σ L V ρ`. Establish `hinj : Function.Injective ((Dinv σ ρ).subtype.baseChange L)`. Rewrite using `[LinearMap.baseChange_eq_ltensor]`. Conclude with `Module.Flat.lTensor_preserves_injective_linearMap _ (Dinv σ ρ).injective_subtype`.

Use `⟨fun e hadm => ?_, fun q n T hA x hx => ?_⟩` and prove the remaining obligations. Unfold `admitted at hadm ⊢`. Rewrite using `[← LinearEquiv.finrank_map_eq (AlgebraTensorModule.assoc F F L L V B), hD, Module.finrank_baseChange]`. Rewrite using `[← hadm]`. Express the relevant statement in the definitionally equal form `Module.finrank L (LinearMap.range ((Dinv σ ρ).subtype.baseChange L)) = _`.

Rewrite using `[LinearMap.finrank_range_of_inj hinj, Module.finrank_baseChange]`. Unfold `AnnD at hA dsimp only`. Establish `comm : ∀ (f : V →ₗ[F] V) (g : B →ₗ[F] B) (y : (L ⊗[F] V) ⊗[F] B), AlgebraTensorModule.assoc F F L L V B (AlgebraTensorModule.map (f.baseChange L) g y) = (AlgebraTensorModule.map f g).lTensor L (AlgebraTensorModule.assoc F F L L V B y)`. Introduce `f g y`. Proceed by induction on `y using TensorProduct.induction_on with`.

Consider the case `zero => simp`. Consider the case `tmul u b`. Proceed by induction on `u using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a v => simp`.

Consider the case `add u₁ u₂ h₁ h₂ => simp only [TensorProduct.add_tmul, map_add, h₁, h₂]`. Consider the case `add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]`. Establish `hmem : AlgebraTensorModule.assoc F F L L V B x ∈ (Dinv σ ρ).baseChange L`. Rewrite using `[← hD]`. Conclude with `Submodule.mem_map_of_mem hx`.

Apply `(AlgebraTensorModule.assoc F F L L V B).injective` to reduce the goal to its premises. Rewrite using `[map_sum, map_zero]`. Simplify using `only [map_zsmul, comm]`. Take `⟨z, hz⟩` from `Submodule.toBaseChange_surjective' L (Dinv σ ρ) hmem`. Rewrite using `[← hz]`.

Use `clear hz hmem`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul a w`. Simplify using `only [Submodule.coe_toBaseChange_tmul, LinearMap.lTensor_tmul]`.

Use `hA w w.2` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [map_sum, map_zsmul, TensorProduct.mk_apply]`. Use `_ = 0 := by rw [this, map_zero]`. Consider the case `add z₁ z₂ h₁ h₂ => simp only [map_add, Submodule.coe_add, Finset.sum_add_distrib, smul_add, h₁, h₂, add_zero]`.
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
