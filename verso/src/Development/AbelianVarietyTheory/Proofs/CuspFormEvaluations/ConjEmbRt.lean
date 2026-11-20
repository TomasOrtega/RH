import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsMemRowHighestTotalDegreeEqTwo

namespace GlobalTheory.ConjugateEmbeddingSquareRoot

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Establish `hre : z.re * z.re - z.im * z.im = -r`. Use `congrArg Complex.re h` as an intermediate fact. Simplify `this` using `[pow_two]`. Establish `him : z.re * z.im + z.im * z.re = 0`. Use `congrArg Complex.im h` as an intermediate fact.

Simplify `this` using `[pow_two]`. Establish `h0 : z.re = 0`. Establish `hm : z.re * z.im = 0` using `by linarith`. Break down `mul_eq_zero.mp hm with h1 | h1` into its components or cases. Conclude with `h1`.

Rewrite `hre` using `[h1]`. Use polynomial arithmetic with `[mul_self_nonneg z.re]`. Apply `Complex.ext` to reduce the goal to its premises. Simplify using `[h0]`. Simplify using the standard rewrite rules.
-/
theorem conj_eq_neg_of_sq {z : ℂ} {r : ℝ} (hr : 0 < r) (h : z ^ 2 = -(r : ℂ)) :
    (starRingEnd ℂ) z = -z := by
  have hre : z.re * z.re - z.im * z.im = -r := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have him : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have h0 : z.re = 0 := by
    have hm : z.re * z.im = 0 := by linarith
    rcases mul_eq_zero.mp hm with h1 | h1
    · exact h1
    · rw [h1] at hre
      nlinarith [mul_self_nonneg z.re]
  apply Complex.ext
  · simp [h0]
  · simp

/- English proof (translation)
Establish `hd : (0 : ℝ) < (H.d : ℝ)` using `by exact_mod_cast H.d_prime.pos`. Establish `h1 : ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact. Simplify using `using this`. Establish `h2 : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ)) : ℂ)`.

Rewrite using `[← map_pow, h1]`. Simplify using the standard rewrite rules. Conclude with `conj_eq_neg_of_sq hd h2`.
-/
theorem conjEmb_rt {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (τ : E →+* ℂ) :
    conjEmb τ (H.rt : E) = -τ (H.rt : E) := by
  have hd : (0 : ℝ) < (H.d : ℝ) := by exact_mod_cast H.d_prime.pos
  have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h2 : (τ (H.rt : E)) ^ 2 = -(((H.d : ℝ)) : ℂ) := by
    rw [← map_pow, h1]
    simp
  exact conj_eq_neg_of_sq hd h2

end GlobalTheory.ConjugateEmbeddingSquareRoot
