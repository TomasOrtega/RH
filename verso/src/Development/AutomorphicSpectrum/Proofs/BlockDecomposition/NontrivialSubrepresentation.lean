import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIrreducibleSecondFactorOfIrreducibleProduct
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.DegPrinSeries

/- English proof (translation)
Introduce `k _ _ _ _ a b χ₁ χ₂ hχ₁ hχ₂`. Establish `hdetChar : ∀ (m : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ → GlobalTheory.PRep.IsSmooth (GlobalTheory.SmGL.detRep (Fin m) χ)`. Introduce `m χ hχ`. Establish `hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)`. Rewrite using `[Units.continuous_iff]`.

Prove the components needed by the constructor for the conclusion. Establish `hval : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)) = fun g : GL (Fin m) k => Matrix.det (g : Matrix (Fin m) (Fin m) k)`. Use function extensionality and compare the values at `g`. Conclude with `Matrix.GeneralLinearGroup.val_det_apply g`. Rewrite using `[hval]`.

Conclude with `Units.continuous_val.matrix_det`. Establish `hinv : (fun g : GL (Fin m) k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) = fun g => Matrix.det ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k)`. Use function extensionality and compare the values at `g`. Rewrite using `[← map_inv, Matrix.GeneralLinearGroup.val_det_apply]`. Rewrite using `[hinv]`.

Conclude with `Units.continuous_coe_inv.matrix_det`. Unfold `GlobalTheory.SmGL.detRep`. Rewrite using `[GlobalTheory.SmGL.isSmooth_ofChar_iff]`. Unfold `GlobalTheory.SmGL.IsSmoothChar at hχ ⊢`. Conclude with `hc.isOpen_preimage _ hχ`.

Establish `hsmooth` using `GlobalTheory.SmGL.isSmooth_comp (GlobalTheory.SmGL.isSmooth_extTensor (hdetChar a χ₁ hχ₁) (hdetChar b χ₂ hχ₂)) (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm.toMonoidHom (by exact (continuous_apply Bool.false).prodMk (continuous_apply Bool.true))`. Establish `hu : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0`. Introduce `h0`. Use `congrArg (TensorProduct.lid ℂ ℂ) h0` as an intermediate fact. Simplify using `at this`.

Take `⟨f, hf1, -⟩` from `GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : a + b = a + b))) _ hsmooth ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))`. Use `⟨⟨⟨⊥, fun g ⦃v⦄ hv => ?_⟩, ⟨⊤, fun _ ⦃_⦄ _ => Submodule.mem_top⟩, fun hEq => ?_⟩⟩` and prove the remaining obligations. Rewrite `hv`, the goal using `[Submodule.mem_bot]`. Rewrite using `[hv, map_zero]`. Establish `hsub` using `congrArg Subrepresentation.toSubmodule hEq`.

Establish `hf : f = 0` using `(Submodule.mem_bot ℂ).1 (Submodule.eq_top_iff'.1 hsub f)`. Rewrite `hf1` using `[hf]`. Apply `hu` to reduce the goal to its premises. Rewrite using `[← hf1]`. Use `first`.

Consider the case `rfl`. Consider the case `simp`.
-/
theorem nontrivial_subrepresentation : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → Nontrivial (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b))) ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom))) := by
  intro k _ _ _ _ a b χ₁ χ₂ hχ₁ hχ₂
  have hdetChar : ∀ (m : ℕ) (χ : kˣ →* ℂˣ), GlobalTheory.SmGL.IsSmoothChar χ →
      GlobalTheory.PRep.IsSmooth (GlobalTheory.SmGL.detRep (Fin m) χ) := by
    intro m χ hχ
    have hc : Continuous (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ) := by
      rw [Units.continuous_iff]
      constructor
      · have hval : (Units.val ∘ (Matrix.GeneralLinearGroup.det : GL (Fin m) k → kˣ)) =
            fun g : GL (Fin m) k => Matrix.det (g : Matrix (Fin m) (Fin m) k) := by
          funext g
          exact Matrix.GeneralLinearGroup.val_det_apply g
        rw [hval]
        exact Units.continuous_val.matrix_det
      · have hinv : (fun g : GL (Fin m) k => ((Matrix.GeneralLinearGroup.det g)⁻¹ : kˣ).val) =
            fun g => Matrix.det ((g⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) := by
          funext g
          rw [← map_inv, Matrix.GeneralLinearGroup.val_det_apply]
        rw [hinv]
        exact Units.continuous_coe_inv.matrix_det
    unfold GlobalTheory.SmGL.detRep
    rw [GlobalTheory.SmGL.isSmooth_ofChar_iff]
    unfold GlobalTheory.SmGL.IsSmoothChar at hχ ⊢
    exact hc.isOpen_preimage _ hχ
  have hsmooth := GlobalTheory.SmGL.isSmooth_comp
    (GlobalTheory.SmGL.isSmooth_extTensor (hdetChar a χ₁ hχ₁) (hdetChar b χ₂ hχ₂))
    (GlobalTheory.SmGL.leviTwo k (Fin a) (Fin b)).symm.toMonoidHom
    (by exact (continuous_apply Bool.false).prodMk (continuous_apply Bool.true))
  have hu : ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ)) ≠ 0 := by
    intro h0
    have := congrArg (TensorProduct.lid ℂ ℂ) h0
    simp at this
  obtain ⟨f, hf1, -⟩ := GlobalTheory.SmGL.ProdIrr.exists_indSp_apply_one
    (GlobalTheory.SmGL.two (GlobalTheory.SmGL.stdSum (rfl : a + b = a + b))) _
    hsmooth ((1 : ℂ) ⊗ₜ[ℂ] (1 : ℂ))
  refine ⟨⟨⟨⊥, fun g ⦃v⦄ hv => ?_⟩, ⟨⊤, fun _ ⦃_⦄ _ => Submodule.mem_top⟩, fun hEq => ?_⟩⟩
  · rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]
  · have hsub := congrArg Subrepresentation.toSubmodule hEq
    have hf : f = 0 := (Submodule.mem_bot ℂ).1 (Submodule.eq_top_iff'.1 hsub f)
    rw [hf] at hf1
    apply hu
    rw [← hf1]
    first
    | rfl
    | simp

end GlobalTheory.CompanionTheory.DegPrinSeries
end
