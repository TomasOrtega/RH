import Mathlib
open Matrix Polynomial

namespace GlobalTheory

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Matrix.mul_apply]`.
-/
theorem gramChange_gram_eq_mul {K : Type} [Field K] (σ : K →+* K) {n : ℕ} {ι : Type} [Fintype ι]
    (u : ι → Fin n → K) :
    (Matrix.of fun i j => ∑ k, σ (u i k) * u j k) = (Matrix.of u).map σ * (Matrix.of u)ᵀ := by
  ext i j
  simp [Matrix.mul_apply]

/- English proof (translation)
Set `b` to `Module.Basis.span hu`. Set `P : Matrix ι ι K` to `Matrix.of fun i a => b.repr ⟨v i, hvu i⟩ a`. Establish `hV : ∀ i, v i = ∑ a, P i a • u a`. Introduce `i`. Establish `h` using `congrArg Subtype.val (b.sum_repr ⟨v i, hvu i⟩)`.

Rewrite `h` using `[Submodule.coe_sum]`. Simplify using `only [Submodule.coe_smul, b, Module.Basis.span_apply] at h`. Conclude with `h.symm`. Establish `hVm : Matrix.of v = P * Matrix.of u`. Use extensionality with `i k`.

Rewrite using `[Matrix.mul_apply, Matrix.of_apply, show v i k = (∑ a, P i a • u a) k from congrFun (hV i) k]`. Simplify using `[Finset.sum_apply]`. Use `⟨P.det, ?_, ?_⟩` and prove the remaining obligations. Introduce `hd`. Take `⟨w, hw0, hw⟩` from `Matrix.exists_vecMul_eq_zero_iff.mpr hd`.

Establish `h1 : w ᵥ* Matrix.of v = 0`. Rewrite using `[hVm, ← Matrix.vecMul_vecMul, hw, Matrix.zero_vecMul]`. Establish `h2 : ∑ i, w i • v i = 0`. Rewrite using `[← h1]`. Use extensionality with `k`.

Simplify using `[Matrix.vecMul, dotProduct, Finset.sum_apply]`. Conclude with `hw0 (funext fun i => Fintype.linearIndependent_iff.mp hv w h2 i)`. Rewrite using `[gramChange_gram_eq_mul, gramChange_gram_eq_mul, hVm, Matrix.map_mul, transpose_mul, show P.map σ * (Matrix.of u).map σ * ((Matrix.of u)ᵀ * Pᵀ) = P.map σ * ((Matrix.of u).map σ * (Matrix.of u)ᵀ) * Pᵀ by`. Simplify using `only [Matrix.mul_assoc],`. Use the proof step `det_mul, det_mul, det_transpose, RingHom.map_det,`.

Use the proof step `RingHom.mapMatrix_apply]`. Expand and normalize the polynomial expressions, which then agree.
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
Introduce `hu hsu hu' hsu'`. Establish `hc : Fintype.card ι' = Fintype.card ι`. Rewrite using `[← finrank_span_eq_card hu', ← finrank_span_eq_card hu, hsu', hsu]`. Set `e : ι' ≃ ι` to `Fintype.equivOfCardEq hc`. Establish `hvu : ∀ i, (u' ∘ e.symm) i ∈ Submodule.span K (Set.range u)`.

Introduce `i`. Rewrite using `[hsu, ← hsu']`. Conclude with `Submodule.subset_span ⟨e.symm i, rfl⟩`. Take `⟨d, hd, hdet⟩` from `gramChange_square σ u (u' ∘ e.symm) hu (hu'.comp e.symm e.symm.injective) hvu`. Use `⟨d, hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hdet, ← det_submatrix_equiv_self e.symm]`. Both sides reduce to the same expression.
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
