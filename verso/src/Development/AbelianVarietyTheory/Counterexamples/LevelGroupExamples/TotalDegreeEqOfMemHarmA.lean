import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.ThProps

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ThetaRuleCheck
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField MvPolynomial

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

/- English proof (translation)
Establish `hd : (0 : ℝ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2`. Rewrite using `[H.sqrt_neg_disc_sq, ← map_pow]`. Establish `: ((H.rt : E)) ^ 2 = -(H.d : E)`. Use `congrArg (algebraMap (𝓞 E) E) H.rt_sq` as an intermediate fact.

Simplify using `using this`. Rewrite using `[this]`. Simplify using the standard rewrite rules. Establish `h2 : starRingEnd ℂ H.rt0 = -H.rt0`. Establish `h` using `H.sqrt_neg_disc_sq`.

Establish `hre` using `congrArg Complex.re h`. Establish `him` using `congrArg Complex.im h`. Simplify using `[pow_two] at hre him`. Establish `: H.rt0.re = 0`. Assume the negation of the conclusion as `hne`.

Establish `: H.rt0.im = 0`. Establish `: H.rt0.re * H.rt0.im = 0` using `by linarith`. Conclude with `(mul_eq_zero.1 this).resolve_left hne`. Rewrite `hre` using `[this]`. Use polynomial arithmetic with `[mul_self_nonneg H.rt0.re]`.

Apply the tactic sequence `apply Complex.ext <;> simp [this]`. Establish `h0 : H.rt0 ≠ -H.rt0`. Introduce `h`. Establish `: H.rt0 = 0` using `by linear_combination h / 2`. Establish `h'` using `H.sqrt_neg_disc_sq`.

Rewrite `h'` using `[this]`. Establish `: (H.d : ℂ) = 0` using `by linear_combination h'`. Conclude with `H.d_prime.ne_zero (by exact_mod_cast this)`. Simplify using `only [InPsi, ComplexEmbedding.conjugate_coe_eq]`. Apply the tactic sequence `rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h]`.

Rewrite using `[h2]`. Simplify using `[h0.symm]`. Rewrite using `[map_neg, h2]`. Simplify using `[h0.symm]`.
-/
theorem inPsi_conjugate_iff (τ : E →+* ℂ) : InPsi H (ComplexEmbedding.conjugate τ) ↔ ¬ InPsi H τ := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have h1 : τ (H.rt : E) ^ 2 = H.rt0 ^ 2 := by
    rw [H.sqrt_neg_disc_sq, ← map_pow]
    have : ((H.rt : E)) ^ 2 = -(H.d : E) := by
      have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
      simpa using this
    rw [this]; simp
  have h2 : starRingEnd ℂ H.rt0 = -H.rt0 := by
    have h := H.sqrt_neg_disc_sq
    have hre := congrArg Complex.re h
    have him := congrArg Complex.im h
    simp [pow_two] at hre him
    have : H.rt0.re = 0 := by
      by_contra hne
      have : H.rt0.im = 0 := by
        have : H.rt0.re * H.rt0.im = 0 := by linarith
        exact (mul_eq_zero.1 this).resolve_left hne
      rw [this] at hre
      nlinarith [mul_self_nonneg H.rt0.re]
    apply Complex.ext <;> simp [this]
  have h0 : H.rt0 ≠ -H.rt0 := by
    intro h
    have : H.rt0 = 0 := by linear_combination h / 2
    have h' := H.sqrt_neg_disc_sq
    rw [this] at h'
    have : (H.d : ℂ) = 0 := by linear_combination h'
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  simp only [InPsi, ComplexEmbedding.conjugate_coe_eq]
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 h1 with h | h <;> rw [h]
  · rw [h2]; simp [h0.symm]
  · rw [map_neg, h2]; simp [h0.symm]

end GlobalTheory.ThetaRuleCheck
