import Mathlib

namespace GlobalTheory.ConjNegSquareNat

/- English proof (translation)
Establish `hre` using `congrArg Complex.re h`. Establish `him` using `congrArg Complex.im h`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`. Establish `hd' : (0 : ℝ) < (d : ℝ)` using `by exact_mod_cast hd`. Establish `h0 : z.re = 0`.

Establish `hm : z.re * z.im = 0` using `by linarith`. Break down `mul_eq_zero.mp hm with h1 | h1` into its components or cases. Conclude with `h1`. It suffices to derive a contradiction. Rewrite `hre` using `[h1]`.

Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem conj_eq_neg_of_sq_eq_neg_nat {z : ℂ} {d : ℕ} (hd : (0 : ℕ) < d)
    (h : z ^ (2 : ℕ) = -(↑d : ℂ)) : (starRingEnd ℂ : ℂ → ℂ) z = -z := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have hd' : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h0 : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hm with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp

end GlobalTheory.ConjNegSquareNat
