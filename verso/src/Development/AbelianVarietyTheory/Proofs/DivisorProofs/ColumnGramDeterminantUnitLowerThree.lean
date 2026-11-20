import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

/- English proof (translation)
Introduce `M hd hu`. Establish `h00` using `hd 0`. Establish `h11` using `hd 1`. Establish `h22` using `hd 2`. Establish `h01 : M 0 1 = 0` using `hu 0 1 (by decide)`.

Establish `h02 : M 0 2 = 0` using `hu 0 2 (by decide)`. Establish `h12 : M 1 2 = 0` using `hu 1 2 (by decide)`. Establish `e1 : lminor (Mᴴ * M) 1 = (Mᴴ * M) 0 0`. Unfold `lminor`. Conclude with `Matrix.det_fin_one _`.

Establish `e2 : lminor (Mᴴ * M) 2 = (Mᴴ * M) 0 0 * (Mᴴ * M) 1 1 - (Mᴴ * M) 0 1 * (Mᴴ * M) 1 0`. Unfold `lminor`. Conclude with `Matrix.det_fin_two _`. Establish `g1 : lminor (Mᴴ * M) 1 = ((1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[e1]`.

Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22, h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]`. Apply the tactic sequence `apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring`. Establish `g2 : lminor (Mᴴ * M) 2 = ((1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[e2]`. Simplify using `only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22, h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]`.

Apply the tactic sequence `apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im] <;> ring`. Establish `pos : ∀ x : ℝ, 0 ≤ x → ‖((1 + x : ℝ) : ℂ)‖ = 1 + x`. Introduce `x hx`. Rewrite using `[Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Unfold `colGram`. Rewrite using `[g1, add_assoc, pos _ (by positivity), ← add_assoc]`. Unfold `colGram`. Rewrite using `[g2, add_assoc, pos _ (by positivity), ← add_assoc]`.
-/
theorem colGram_three_unitLower : ∀ M : Matrix (Fin 3) (Fin 3) ℂ, (∀ i, M i i = 1) →
    (∀ i j : Fin 3, i < j → M i j = 0) →
    colGram M 1 = 1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 ∧
      colGram M 2 = 1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 := by
  intro M hd hu
  have h00 := hd 0
  have h11 := hd 1
  have h22 := hd 2
  have h01 : M 0 1 = 0 := hu 0 1 (by decide)
  have h02 : M 0 2 = 0 := hu 0 2 (by decide)
  have h12 : M 1 2 = 0 := hu 1 2 (by decide)
  have e1 : lminor (Mᴴ * M) 1 = (Mᴴ * M) 0 0 := by
    unfold lminor
    exact Matrix.det_fin_one _
  have e2 : lminor (Mᴴ * M) 2 =
      (Mᴴ * M) 0 0 * (Mᴴ * M) 1 1 - (Mᴴ * M) 0 1 * (Mᴴ * M) 1 0 := by
    unfold lminor
    exact Matrix.det_fin_two _
  have g1 : lminor (Mᴴ * M) 1 = ((1 + ‖M 1 0‖ ^ 2 + ‖M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e1]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  have g2 : lminor (Mᴴ * M) 2 =
      ((1 + ‖M 2 1‖ ^ 2 + ‖M 1 0 * M 2 1 - M 2 0‖ ^ 2 : ℝ) : ℂ) := by
    rw [e2]
    simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.conjTranspose_apply, h00, h11, h22,
      h01, h02, h12, Complex.sq_norm, Complex.normSq_apply]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im]
      <;> ring
  have pos : ∀ x : ℝ, 0 ≤ x → ‖((1 + x : ℝ) : ℂ)‖ = 1 + x := by
    intro x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  refine ⟨?_, ?_⟩
  · unfold colGram
    rw [g1, add_assoc, pos _ (by positivity), ← add_assoc]
  · unfold colGram
    rw [g2, add_assoc, pos _ (by positivity), ← add_assoc]

end GlobalTheory.IntBall
