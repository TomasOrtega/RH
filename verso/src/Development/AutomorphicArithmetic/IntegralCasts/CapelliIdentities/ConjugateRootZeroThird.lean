import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot

/- English proof (translation)
Introduce `E _ _ _ H`. Establish `hd : (0 : ℝ) < (H.d : ℝ)` using `by exact_mod_cast H.d_prime.pos`. Establish `h` using `H.sqrt_neg_disc_sq`. Establish `hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ)`. Simplify `congrArg Complex.re h` using `[pow_two, Complex.mul_re]`.

Establish `him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0`. Simplify `congrArg Complex.im h` using `[pow_two, Complex.mul_im]`. Establish `ha : H.rt0.re = 0`. Assume the negation of the conclusion as `ha`. Establish `hm : H.rt0.re * H.rt0.im = 0` using `by linarith`.

Establish `hb : H.rt0.im = 0` using `(mul_eq_zero.mp hm).resolve_left ha`. Rewrite `hre` using `[hb]`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[ha]`.

Simplify using the standard rewrite rules.
-/
theorem UpperTheory.Reformulated.B.StarRingEndRootEqNeg.rt0_conj_neg_ne_zero :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : NumberField.IsCMField E]
      (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E), (starRingEnd ℂ : ℂ → ℂ) H.rt0 = -H.rt0 := by
  intro E _ _ _ H
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h := H.sqrt_neg_disc_sq
  have hre : H.rt0.re * H.rt0.re - H.rt0.im * H.rt0.im = -(H.d : ℝ) := by
    simpa [pow_two, Complex.mul_re] using congrArg Complex.re h
  have him : H.rt0.re * H.rt0.im + H.rt0.im * H.rt0.re = 0 := by
    simpa [pow_two, Complex.mul_im] using congrArg Complex.im h
  have ha : H.rt0.re = 0 := by
    by_contra ha
    have hm : H.rt0.re * H.rt0.im = 0 := by linarith
    have hb : H.rt0.im = 0 := (mul_eq_zero.mp hm).resolve_left ha
    rw [hb] at hre
    nlinarith [mul_self_nonneg H.rt0.re]
  apply Complex.ext
  · simp [ha]
  · simp
