import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndEnc

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h1` using `congrArg Complex.re H.sqrt_neg_disc_sq`. Establish `h2` using `congrArg Complex.im H.sqrt_neg_disc_sq`. Simplify using `only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re, Complex.natCast_im, neg_zero] at h1 h2`. Establish `hre : H.rt0.re = 0`.

Break down `mul_eq_zero.1 (show H.rt0.re * H.rt0.im * 2 = 0 by linarith) with h | h` into its components or cases. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Rewrite `h1` using `[h]`.

Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`. Evaluate the numerical expressions using `at h`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[hre]`. Simplify using the standard rewrite rules.
-/
theorem rt0_conj_neg_ne_zero (H : Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 := congrArg Complex.re H.sqrt_neg_disc_sq
  have h2 := congrArg Complex.im H.sqrt_neg_disc_sq
  simp only [pow_two, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.natCast_re,
    Complex.natCast_im, neg_zero] at h1 h2
  have hre : H.rt0.re = 0 := by
    rcases mul_eq_zero.1 (show H.rt0.re * H.rt0.im * 2 = 0 by linarith) with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact h
      · exfalso
        rw [h] at h1
        nlinarith [mul_self_nonneg H.rt0.re]
    · norm_num at h
  apply Complex.ext
  · simp [hre]
  · simp

/- English proof (translation)
Introduce `τ`. Establish `hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ)`. Establish `e : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq` as an intermediate fact. Simplify using `using this`.

Rewrite using `[← map_pow, e]`. Simplify using the standard rewrite rules. Establish `hpm : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0`. Establish `h : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0`. Establish `e : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = τ (H.rt : E) ^ 2 - H.rt0 ^ 2` using `by ring`.

Rewrite using `[e, hsq, H.sqrt_neg_disc_sq, sub_self]`. Break down `mul_eq_zero.1 h with h | h` into its components or cases. Conclude with `Or.inl (sub_eq_zero.1 h)`. Conclude with `Or.inr (eq_neg_of_add_eq_zero_left h)`. Break down `hpm with h | h` into its components or cases.

Conclude with `Or.inl h`. Use `right show starRingEnd ℂ (τ (H.rt : E)) = H.rt0`. Rewrite using `[h, map_neg, rt0_conj_neg_ne_zero, neg_neg]`.
-/
theorem psiCover_holds (H : Host E) : PsiCoverSt H := by
  intro τ
  have hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have e : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (fun x : 𝓞 E => (x : E)) H.rt_sq
      simpa using this
    rw [← map_pow, e]
    simp
  have hpm : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
    have h : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = 0 := by
      have e : (τ (H.rt : E) - H.rt0) * (τ (H.rt : E) + H.rt0) = τ (H.rt : E) ^ 2 - H.rt0 ^ 2 := by ring
      rw [e, hsq, H.sqrt_neg_disc_sq, sub_self]
    rcases mul_eq_zero.1 h with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  rcases hpm with h | h
  · exact Or.inl h
  · right
    show starRingEnd ℂ (τ (H.rt : E)) = H.rt0
    rw [h, map_neg, rt0_conj_neg_ne_zero, neg_neg]

end Formalism.MainNotions.ModuliIntegralCharts.H1
