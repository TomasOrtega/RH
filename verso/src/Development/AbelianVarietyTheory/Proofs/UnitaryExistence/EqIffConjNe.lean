import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature

namespace GlobalTheory.ConjugateMembership

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Establish `hre : x.re * x.re - x.im * x.im = -d`. Use `congrArg Complex.re hx` as an intermediate fact. Simplify `this` using `[sq]`. Establish `him : x.re * x.im + x.im * x.re = 0`. Use `congrArg Complex.im hx` as an intermediate fact.

Simplify `this` using `[sq]`. Establish `h0 : x.re = 0`. Assume the negation of the conclusion as `h`. Establish `hi : x.im = 0`. Establish `h2 : x.re * x.im = 0` using `by linarith`.

Conclude with `(mul_eq_zero.1 h2).resolve_left h`. Rewrite `hre` using `[hi]`. Use polynomial arithmetic with `[mul_self_nonneg x.re]`. Apply the tactic sequence `apply Complex.ext <;> simp [h0]`.
-/
theorem conj_eq_neg_of_sq {x : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) :
    (starRingEnd ℂ) x = -x := by
  have hre : x.re * x.re - x.im * x.im = -d := by
    have := congrArg Complex.re hx
    simpa [sq] using this
  have him : x.re * x.im + x.im * x.re = 0 := by
    have := congrArg Complex.im hx
    simpa [sq] using this
  have h0 : x.re = 0 := by
    by_contra h
    have hi : x.im = 0 := by
      have h2 : x.re * x.im = 0 := by linarith
      exact (mul_eq_zero.1 h2).resolve_left h
    rw [hi] at hre
    nlinarith [mul_self_nonneg x.re]
  apply Complex.ext <;> simp [h0]

/- English proof (translation)
Rewrite using `[conj_eq_neg_of_sq hd hx]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl h`. Establish `h0 : x = 0` using `by linear_combination (-1 / 2 : ℂ) * h`. Rewrite `hx` using `[h0]`.

Establish `: (d : ℂ) = 0` using `by linear_combination hx`. Conclude with `hd.ne' (by exact_mod_cast this)`. Introduce `h`. Establish `: (x - r) * (-x - r) = 0` using `by linear_combination hr - hx`. Break down `mul_eq_zero.1 this with h1 | h1` into its components or cases.

Conclude with `sub_eq_zero.1 h1`. Conclude with `absurd (sub_eq_zero.1 h1) h`.
-/
theorem eq_iff_conj_ne {x r : ℂ} {d : ℝ} (hd : 0 < d) (hx : x ^ 2 = -(d : ℂ)) (hr : r ^ 2 = -(d : ℂ)) :
    x = r ↔ ¬ (starRingEnd ℂ) x = r := by
  rw [conj_eq_neg_of_sq hd hx]
  constructor
  · rintro rfl h
    have h0 : x = 0 := by linear_combination (-1 / 2 : ℂ) * h
    rw [h0] at hx
    have : (d : ℂ) = 0 := by linear_combination hx
    exact hd.ne' (by exact_mod_cast this)
  · intro h
    have : (x - r) * (-x - r) = 0 := by linear_combination hr - hx
    rcases mul_eq_zero.1 this with h1 | h1
    · exact sub_eq_zero.1 h1
    · exact absurd (sub_eq_zero.1 h1) h

/- English proof (translation)
Establish `hd : (0 : ℝ) < (H.d : ℝ)` using `by exact_mod_cast H.d_prime.pos`. Establish `hE : (H.rt : E) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `hx : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ) : ℂ))`.

Rewrite using `[← map_pow, hE]`. Simplify using the standard rewrite rules. Establish `hr : H.rt0 ^ 2 = -(((H.d : ℝ) : ℂ))`. Rewrite using `[H.sqrt_neg_disc_sq]`. Simplify using the standard rewrite rules.

Rewrite using `[hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]`. Conclude with `eq_iff_conj_ne hd hx hr`.
-/
theorem mem_iff_conjugate_notMem {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (Ψ : Finset (E →+* ℂ)) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ τ (H.rt : E) = H.rt0) (τ : E →+* ℂ) :
    τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have hE : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have hx : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [← map_pow, hE]; simp
  have hr : H.rt0 ^ 2 = -(((H.d : ℝ) : ℂ)) := by
    rw [H.sqrt_neg_disc_sq]; simp
  rw [hΨ, hΨ, ComplexEmbedding.conjugate_coe_eq]
  exact eq_iff_conj_ne hd hx hr

end GlobalTheory.ConjugateMembership
