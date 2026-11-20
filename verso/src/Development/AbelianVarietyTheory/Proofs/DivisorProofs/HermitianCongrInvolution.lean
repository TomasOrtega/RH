import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousFourierGau
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory

open MeasureTheory Complex Matrix in
open scoped RealInnerProductSpace ContDiff Real ComplexOrder in

/- English proof (translation)
Establish `hA : H.IsHermitian` using `hH`. Use `set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU`. Use `set d := hA.eigenvalues with hdd`. Establish `hd0 : ∀ i, d i ≠ 0`. Introduce `i hi`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[hA.det_eq_prod_eigenvalues]`. Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hdd, hi]; simp)`. Use `set s : Matrix ι ι ℂ := diagonal fun i => if 0 < d i then 1 else -1 with hs`. Use `set D : Matrix ι ι ℂ := diagonal fun i => ((Real.sqrt |d i| : ℝ) : ℂ) with hD`.

Establish `key : D * s * D = diagonal (RCLike.ofReal ∘ d)`. Rewrite using `[hD, hs, diagonal_mul_diagonal, diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Establish `hsq : ((Real.sqrt |d i| : ℝ) : ℂ) * ((Real.sqrt |d i| : ℝ) : ℂ) = ((|d i| : ℝ) : ℂ)`.

Rewrite using `[← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]`. Simplify using `only [Function.comp_apply]`. Use `split_ifs with h`. Rewrite using `[mul_one, hsq, abs_of_pos h]`. Both sides reduce to the same expression.

Rewrite using `[mul_neg_one, neg_mul, hsq, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hd0 i))] push_cast`. Put the polynomial expressions in normal form. Both sides reduce to the same expression. Establish `hDH : Dᴴ = D`. Rewrite using `[hD, diagonal_conjTranspose]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Establish `hsH : sᴴ = s`. Apply the tactic sequence `rw [hs, diagonal_conjTranspose]; congr 1; funext i; by_cases h : 0 < d i <;> simp [h]`.

Establish `hss : s * s = 1`. Apply the tactic sequence `rw [hs, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp`. Establish `hR : (D * star U)ᴴ * s * (D * star U) = H`. Rewrite using `[conjTranspose_mul, hDH, star_eq_conjTranspose, conjTranspose_conjTranspose]`. Use `conv_rhs => rw [hA.spectral_theorem]`.

Rewrite using `[Unitary.conjStarAlgAut_apply, ← key]`. Simplify using `only [Matrix.mul_assoc, star_eq_conjTranspose]`. Both sides reduce to the same expression. Use `⟨D * star U, s, ?_, hsH, hss, hR⟩` and prove the remaining obligations. Introduce `h0`.

Apply `hd` to reduce the goal to its premises. Rewrite using `[← hR, det_mul, det_mul, h0, mul_zero]`.
-/
theorem _root_.GlobalTheory.hermitian_congr_involution (ι : Type) [Fintype ι] [DecidableEq ι]
    (H : Matrix ι ι ℂ) (hH : Hᴴ = H) (hd : H.det ≠ 0) :
    ∃ R s : Matrix ι ι ℂ, R.det ≠ 0 ∧ sᴴ = s ∧ s * s = 1 ∧ Rᴴ * s * R = H := by
  have hA : H.IsHermitian := hH
  set U : Matrix ι ι ℂ := (hA.eigenvectorUnitary : Matrix ι ι ℂ) with hU
  set d := hA.eigenvalues with hdd
  have hd0 : ∀ i, d i ≠ 0 := by
    intro i hi
    apply hd
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [← hdd, hi]; simp)
  set s : Matrix ι ι ℂ := diagonal fun i => if 0 < d i then 1 else -1 with hs
  set D : Matrix ι ι ℂ := diagonal fun i => ((Real.sqrt |d i| : ℝ) : ℂ) with hD
  have key : D * s * D = diagonal (RCLike.ofReal ∘ d) := by
    rw [hD, hs, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    have hsq : ((Real.sqrt |d i| : ℝ) : ℂ) * ((Real.sqrt |d i| : ℝ) : ℂ) = ((|d i| : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (abs_nonneg _)]
    simp only [Function.comp_apply]
    split_ifs with h
    · rw [mul_one, hsq, abs_of_pos h]; rfl
    · rw [mul_neg_one, neg_mul, hsq, abs_of_neg (lt_of_le_of_ne (not_lt.1 h) (hd0 i))]
      push_cast; ring_nf; rfl
  have hDH : Dᴴ = D := by
    rw [hD, diagonal_conjTranspose]; congr 1; funext i; simp
  have hsH : sᴴ = s := by
    rw [hs, diagonal_conjTranspose]; congr 1; funext i; by_cases h : 0 < d i <;> simp [h]
  have hss : s * s = 1 := by
    rw [hs, diagonal_mul_diagonal, ← diagonal_one]; congr 1; funext i; split_ifs <;> simp
  have hR : (D * star U)ᴴ * s * (D * star U) = H := by
    rw [conjTranspose_mul, hDH, star_eq_conjTranspose, conjTranspose_conjTranspose]
    conv_rhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, ← key]
    simp only [Matrix.mul_assoc, star_eq_conjTranspose]
    rfl
  refine ⟨D * star U, s, ?_, hsH, hss, hR⟩
  intro h0
  apply hd
  rw [← hR, det_mul, det_mul, h0, mul_zero]

end GlobalTheory
