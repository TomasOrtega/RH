import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LocalValuationColumns
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

namespace GlobalTheory.ConjugateMultiplicitySum

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Establish `hd' : (0 : ℝ) < d` using `by exact_mod_cast hd`. Establish `hre : z.re * z.re - z.im * z.im = -(d : ℝ)`. Use `congrArg Complex.re hz` as an intermediate fact. Simplify `this` using `[pow_two]`. Establish `him : z.re * z.im = 0`.

Use `congrArg Complex.im hz` as an intermediate fact. Simplify using `[pow_two] at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hre0 : z.re = 0`. Break down `mul_eq_zero.1 him with h | h` into its components or cases.

Conclude with `h`. Rewrite `hre` using `[h]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Establish `hc : starRingEnd ℂ z = -z`. Apply the tactic sequence `apply Complex.ext <;> simp [hre0]`.

Establish `hz0 : z ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hre`. Conclude with `hd.ne' hre`. Rewrite using `[hc]`.

Prove the components needed by the constructor for the conclusion. Introduce `h1 h2`. Apply `hz0` to reduce the goal to its premises. Establish `: (2 : ℂ) * z = 0` using `by linear_combination h2 - h1`. Simplify using `using this`.

Introduce `h`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 (hz.trans hw.symm) with h1 | h1` into its components or cases. Conclude with `absurd h1 h`. Rewrite using `[h1, neg_neg]`.
-/
theorem conj_eq_iff {z w : ℂ} {d : ℕ} (hd : 0 < d) (hz : z ^ 2 = -(d : ℂ)) (hw : w ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = w ↔ ¬ z = w := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re hz
    simpa [pow_two] using this
  have him : z.re * z.im = 0 := by
    have := congrArg Complex.im hz
    simp [pow_two] at this
    linarith
  have hre0 : z.re = 0 := by
    rcases mul_eq_zero.1 him with h | h
    · exact h
    · rw [h] at hre
      nlinarith [mul_self_nonneg z.re]
  have hc : starRingEnd ℂ z = -z := by
    apply Complex.ext <;> simp [hre0]
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hre
    exact hd.ne' hre
  rw [hc]
  constructor
  · intro h1 h2
    apply hz0
    have : (2 : ℂ) * z = 0 := by linear_combination h2 - h1
    simpa using this
  · intro h
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 (hz.trans hw.symm) with h1 | h1
    · exact absurd h1 h
    · rw [h1, neg_neg]

/- English proof (translation)
Establish `hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ)`. Establish `h` using `congrArg (fun a : 𝓞 E => τ (algebraMap (𝓞 E) E a)) H.rt_sq`. Simplify using `using h`. Establish `key : conjEmb τ (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0` using `conj_eq_iff H.d_prime.pos hsq H.sqrt_neg_disc_sq`. Unfold `Datum.mult`.

Distinguish the cases in `h : τ (H.rt : E) = H.rt0`. Rewrite using `[if_pos h, if_neg (fun h' => key.1 h' h)]`. Rewrite using `[if_neg h, if_pos (key.2 h), add_comm]`.
-/
theorem mult_add_mult_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    (τ : E →+* ℂ) : Datum.mult D τ + Datum.mult D (conjEmb τ) = D.p + D.q := by
  have hsq : (τ (H.rt : E)) ^ 2 = -(H.d : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => τ (algebraMap (𝓞 E) E a)) H.rt_sq
    simpa using h
  have key : conjEmb τ (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0 :=
    conj_eq_iff H.d_prime.pos hsq H.sqrt_neg_disc_sq
  unfold Datum.mult
  by_cases h : τ (H.rt : E) = H.rt0
  · rw [if_pos h, if_neg (fun h' => key.1 h' h)]
  · rw [if_neg h, if_pos (key.2 h), add_comm]

end GlobalTheory.ConjugateMultiplicitySum
