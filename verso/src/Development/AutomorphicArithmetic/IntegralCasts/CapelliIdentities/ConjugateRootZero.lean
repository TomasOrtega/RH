import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

/- English proof (translation)
Introduce `E _ _ _ H`. Establish `h` using `H.sqrt_neg_disc_sq`. Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hre` using `congrArg Complex.re h`. Establish `him` using `congrArg Complex.im h`.

Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him`. Establish `h0 : H.rt0.re * H.rt0.im = 0` using `by linarith`. Establish `hr : H.rt0.re = 0`. Break down `mul_eq_zero.mp h0 with h1 | h1` into its components or cases. Conclude with `h1`.

It suffices to derive a contradiction. Rewrite `hre` using `[h1]`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Apply `Complex.ext` to reduce the goal to its premises. Rewrite using `[Complex.conj_re, Complex.neg_re, hr, neg_zero]`.

Rewrite using `[Complex.conj_im, Complex.neg_im]`.
-/
theorem UpperTheory.Reformulated.B.ComplexConjugateRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have h := H.sqrt_neg_disc_sq
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.natCast_re, Complex.natCast_im, neg_zero] at hre him
  have h0 : H.rt0.re * H.rt0.im = 0 := by linarith
  have hr : H.rt0.re = 0 := by
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exfalso
      rw [h1] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · rw [Complex.conj_re, Complex.neg_re, hr, neg_zero]
  · rw [Complex.conj_im, Complex.neg_im]
