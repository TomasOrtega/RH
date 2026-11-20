import Mathlib

namespace GlobalTheory.ClosingLemmaFourth

/- English proof (translation)
Introduce `z d hd h`. Establish `hdR : (0 : ℝ) < (d : ℝ)` using `by exact_mod_cast hd`. Establish `hre` using `congrArg Complex.re h`. Establish `him` using `congrArg Complex.im h`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`.

Establish `hr : z.re = 0`. Establish `h2 : z.re * z.im = 0` using `by linarith`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases. Conclude with `h3`. Rewrite `hre` using `[h3]`.

Use polynomial arithmetic with `[sq_nonneg z.re]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `apply Complex.ext <;> simp [hr]`. Introduce and unpack `rfl`. Simplify using `at hre`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem main : ∀ {z : ℂ} {d : ℕ}, (0 : ℕ) < d → z ^ (2 : ℕ) = -(↑d : ℂ) →
    (starRingEnd ℂ : ℂ → ℂ) z = -z ∧ z ≠ (0 : ℂ) := by
  intro z d hd h
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hr : z.re = 0 := by
    have h2 : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · rw [h3] at hre
      nlinarith [sq_nonneg z.re]
  refine ⟨?_, ?_⟩
  · apply Complex.ext <;> simp [hr]
  · rintro rfl
    simp at hre
    linarith

end GlobalTheory.ClosingLemmaFourth
