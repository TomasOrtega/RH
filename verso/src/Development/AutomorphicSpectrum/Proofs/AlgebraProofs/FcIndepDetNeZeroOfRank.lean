import Mathlib
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Establish `hs : Function.Surjective B.mulVecLin`. Rewrite using `[← LinearMap.range_eq_top]`. Apply `Submodule.eq_top_of_finrank_eq` to reduce the goal to its premises. Simplify `h` using `[Matrix.rank]`. Establish `hu : IsUnit B` using `Matrix.mulVec_surjective_iff_isUnit.mp hs`.

Conclude with `((Matrix.isUnit_iff_isUnit_det B).mp hu).ne_zero`.
-/
theorem fcIndep_det_ne_zero_of_rank {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (h : B.rank = n) :
    B.det ≠ 0 := by
  have hs : Function.Surjective B.mulVecLin := by
    rw [← LinearMap.range_eq_top]
    apply Submodule.eq_top_of_finrank_eq
    simpa [Matrix.rank] using h
  have hu : IsUnit B := Matrix.mulVec_surjective_iff_isUnit.mp hs
  exact ((Matrix.isUnit_iff_isUnit_det B).mp hu).ne_zero

/- English proof (translation)
Introduce `p q A Φ h0 hA hΦ`. Establish `h1 : (Φᴴ * Φ).det ≠ 0`. Apply `fcIndep_det_ne_zero_of_rank` to reduce the goal to its premises. Use `open ComplexOrder in rw [Matrix.rank_conjTranspose_mul_self, hΦ]`. Establish `h2 : (A * Aᴴ).det ≠ 0`.

Apply `fcIndep_det_ne_zero_of_rank` to reduce the goal to its premises. Use `open ComplexOrder in rw [Matrix.rank_self_mul_conjTranspose, hA]`. Establish `key : ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ, (fromRows N A).det * (fromCols Φ Aᴴ).det = (N * Φ).det * (A * Aᴴ).det`. Introduce `N`. Rewrite using `[← Matrix.det_mul, Matrix.fromRows_mul_fromCols, h0, Matrix.det_fromBlocks_zero₂₁]`.

Establish `h3 : (fromRows Φᴴ A).det * (fromCols Φ Aᴴ).det ≠ 0`. Rewrite using `[key]`. Conclude with `mul_ne_zero h1 h2`. Use `⟨h1, left_ne_zero_of_mul h3, fun N => ?_⟩` and prove the remaining obligations. Apply `mul_right_cancel₀ (right_ne_zero_of_mul h3)` to reduce the goal to its premises.

Establish `a` using `key N`. Establish `b` using `key Φᴴ`. Take the linear combination `(Φᴴ * Φ).det * a - (N * Φ).det * b`.
-/
theorem fcIndep : ∀ (p q : ℕ) (A : Matrix (Fin p) (Fin q ⊕ Fin p) ℂ) (Φ : Matrix (Fin q ⊕ Fin p) (Fin q) ℂ), A * Φ = 0 → A.rank = p → Φ.rank = q → (Φᴴ * Φ).det ≠ 0 ∧ (fromRows Φᴴ A).det ≠ 0 ∧ ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ, (fromRows N A).det * (Φᴴ * Φ).det = (fromRows Φᴴ A).det * (N * Φ).det := by
  intro p q A Φ h0 hA hΦ
  have h1 : (Φᴴ * Φ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_conjTranspose_mul_self, hΦ]
  have h2 : (A * Aᴴ).det ≠ 0 := by
    apply fcIndep_det_ne_zero_of_rank
    open ComplexOrder in rw [Matrix.rank_self_mul_conjTranspose, hA]
  have key : ∀ N : Matrix (Fin q) (Fin q ⊕ Fin p) ℂ,
      (fromRows N A).det * (fromCols Φ Aᴴ).det = (N * Φ).det * (A * Aᴴ).det := by
    intro N
    rw [← Matrix.det_mul, Matrix.fromRows_mul_fromCols, h0, Matrix.det_fromBlocks_zero₂₁]
  have h3 : (fromRows Φᴴ A).det * (fromCols Φ Aᴴ).det ≠ 0 := by
    rw [key]; exact mul_ne_zero h1 h2
  refine ⟨h1, left_ne_zero_of_mul h3, fun N => ?_⟩
  apply mul_right_cancel₀ (right_ne_zero_of_mul h3)
  have a := key N
  have b := key Φᴴ
  linear_combination (Φᴴ * Φ).det * a - (N * Φ).det * b

end GlobalTheory.CompanionTheory.Ar.Flat
