import Mathlib
open Matrix Polynomial

namespace GlobalTheory

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem gramChange_gram_eq_mul {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} [Fintype ι]
    (u : ι → Fin n → K) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k) = (Matrix.of u).map σ * (Matrix.of u)ᵀ := by
  ext i j
  simp [Matrix.mul_apply]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.

Rewrite the hypotheses and the conclusion using the stated equalities. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem gramChange_square {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type}
    [Fintype ι] [DecidableEq ι] (u v : ι → Fin n → K) (hu : LinearIndependent K u)
    (hv : LinearIndependent K v) (hvu : ∀ i, v i ∈ Submodule.span K (Set.range u)) :
    ∃ d : K, d ≠ 0 ∧ (Matrix.of fun i j => ∑ k, σ (v i k) * v j k).det
      = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  classical
  let b := Module.Basis.span hu
  let P : Matrix ι ι K := Matrix.of fun i a => b.repr ⟨v i, hvu i⟩ a
  have hV : ∀ i, v i = ∑ a, P i a • u a := by
    intro i
    have h := congrArg Subtype.val (b.sum_repr ⟨v i, hvu i⟩)
    rw [Submodule.coe_sum] at h
    simp only [Submodule.coe_smul, b, Module.Basis.span_apply] at h
    exact h.symm
  have hVm : Matrix.of v = P * Matrix.of u := by
    ext i k
    rw [Matrix.mul_apply, Matrix.of_apply,
      show v i k = (∑ a, P i a • u a) k from congrFun (hV i) k]
    simp [Finset.sum_apply]
  refine ⟨P.det, ?_, ?_⟩
  · intro hd
    obtain ⟨w, hw0, hw⟩ := Matrix.exists_vecMul_eq_zero_iff.mpr hd
    have h1 : w ᵥ* Matrix.of v = 0 := by
      rw [hVm, ← Matrix.vecMul_vecMul, hw, Matrix.zero_vecMul]
    have h2 : ∑ i, w i • v i = 0 := by
      rw [← h1]
      ext k
      simp [Matrix.vecMul, dotProduct, Finset.sum_apply]
    exact hw0 (funext fun i => Fintype.linearIndependent_iff.mp hv w h2 i)
  · rw [gramChange_gram_eq_mul, gramChange_gram_eq_mul, hVm, Matrix.map_mul, transpose_mul,
      show P.map σ * (Matrix.of u).map σ * ((Matrix.of u)ᵀ * Pᵀ)
        = P.map σ * ((Matrix.of u).map σ * (Matrix.of u)ᵀ) * Pᵀ by
          simp only [Matrix.mul_assoc],
      det_mul, det_mul, det_transpose, RingHom.map_det,
      RingHom.mapMatrix_apply]
    ring

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Introduce a local definition for the expression. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem gram_det_change_of_bases {K : Type} [Field K] (σ : K →+* K) {n : ℕ}
    (W : Submodule K (Fin n → K)) {ι ι' : Type} [Fintype ι] [Fintype ι'] [DecidableEq ι]
    [DecidableEq ι'] (u : ι → Fin n → K) (u' : ι' → Fin n → K) :
    LinearIndependent K u → Submodule.span K (Set.range u) = W → LinearIndependent K u' →
      Submodule.span K (Set.range u') = W → ∃ d : K, d ≠ 0 ∧
        (Matrix.of fun i j => ∑ k, σ (u' i k) * u' j k).det
          = σ d * d * (Matrix.of fun i j => ∑ k, σ (u i k) * u j k).det := by
  intro hu hsu hu' hsu'
  have hc : Fintype.card ι' = Fintype.card ι := by
    rw [← finrank_span_eq_card hu', ← finrank_span_eq_card hu, hsu', hsu]
  let e : ι' ≃ ι := Fintype.equivOfCardEq hc
  have hvu : ∀ i, (u' ∘ e.symm) i ∈ Submodule.span K (Set.range u) := by
    intro i
    rw [hsu, ← hsu']
    exact Submodule.subset_span ⟨e.symm i, rfl⟩
  obtain ⟨d, hd, hdet⟩ := gramChange_square σ u (u' ∘ e.symm) hu
    (hu'.comp e.symm e.symm.injective) hvu
  refine ⟨d, hd, ?_⟩
  rw [← hdet, ← det_submatrix_equiv_self e.symm]
  rfl

end GlobalTheory
