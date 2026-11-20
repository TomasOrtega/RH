import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace GlobalTheory.SkewToHerm

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

A detailed English derivation is pending.
-/
theorem exists_sigma_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) : ∃ x : E, σ x ≠ x := by
  by_contra hc
  push_neg at hc
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hτ : NumberField.ComplexEmbedding.IsReal τ := by
    rw [NumberField.ComplexEmbedding.isReal_iff]
    ext x
    simp only [NumberField.ComplexEmbedding.conjugate_coe_eq]
    have e := h.2.2.2 τ x
    rw [hc x] at e
    exact e.symm
  have hc' := h.2.1.isComplex (NumberField.InfinitePlace.mk τ)
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex] at hc'
  exact hc' ⟨τ, hτ, rfl⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Substitute using the available equality. Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
theorem det_ne_zero_of_hasSig {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (r s : ℕ) (h : HasSig M r s) : M.det ≠ 0 := by
  obtain ⟨hrs, A, hA⟩ := h
  subst hrs
  let e : Fin r ⊕ Fin s ≃ Fin (r + s) := finSumFinEquiv
  let A' : Matrix (Fin (r + s)) (Fin (r + s)) ℂ := A.submatrix id e.symm
  have hA' : A'ᵀ * M * A'.map star = (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).submatrix e.symm e.symm := by
    rw [← hA]
    ext i j
    simp [A', Matrix.mul_apply]
  have hd : (A'ᵀ * M * A'.map star).det ≠ 0 := by
    rw [hA', Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁, Matrix.det_neg]
    simp
  intro h0
  apply hd
  rw [Matrix.det_mul, Matrix.det_mul, h0]
  simp

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem sigma_invol {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [h.2.2.2, h.2.2.2, star_star]

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.
-/
theorem exists_hermND (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hCM : IsCMExt F E σ) (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ) (hW : W.IsSkew σ B r s) :
    ∃ c₀ : E, c₀ ≠ 0 ∧ IsHermND σ (c₀ • W.J.map σ) := by
  obtain ⟨x, hx⟩ := exists_sigma_ne σ hCM
  have hss := sigma_invol σ hCM
  refine ⟨x - σ x, sub_ne_zero.mpr (Ne.symm hx), fun i j => ?_, ?_⟩
  · simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, map_mul, map_sub, hss]
    rw [hW.skew j i]
    ring
  · have hdet : (W.J.map σ).det = σ W.J.det := by rw [AlgHom.map_det]; rfl
    rw [Matrix.det_smul, hdet]
    refine mul_ne_zero (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm hx))) ?_
    rw [map_ne_zero_iff σ σ.toRingHom.injective]
    obtain ⟨w⟩ : Nonempty (NumberField.InfinitePlace F) := inferInstance
    have hd := det_ne_zero_of_hasSig _ r s (hW.sig w)
    have hdτ : (W.J.map (B.emb w).1).det = (B.emb w).1 W.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, hdτ] at hd
    intro h0
    apply hd
    rw [h0, map_zero, mul_zero]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem skew_to_hermND : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (n : ℕ) (W : Spc F E n) (r s : ℕ), W.IsSkew σ B r s → ∃ c₀ : E, c₀ ≠ 0 ∧ IsHermND σ (c₀ • W.J.map σ) :=
  fun F E _ _ _ _ _ σ hCM B n W r s hW => exists_hermND F E σ hCM B n W r s hW

end GlobalTheory.SkewToHerm
