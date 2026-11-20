import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj
open scoped Matrix

namespace GlobalTheory

/- English proof (translation)
Introduce `E _ _ _ ξ ξ' τ h h' hn`. Establish `key : ∀ x : E, cc x = -x → τ (x ^ 2) = -((‖τ x‖ ^ 2 : ℝ) : ℂ)`. Introduce `x hx`. Establish `h1 : τ (cc x) = (starRingEnd ℂ) (τ x)` using `IsCMField.complexEmbedding_complexConj E τ x`. Rewrite `h1` using `[hx, map_neg]`.

Establish `h2` using `Complex.mul_conj' (τ x)`. Rewrite `h2` using `[← h1]`. Rewrite using `[map_pow]`. Use `push_cast`. Take the linear combination `-h2`.

Establish `h3 : τ (ξ' ^ 2) = τ (ξ ^ 2)` using `by rw [key ξ h, key ξ' h', hn]`. Conclude with `sq_eq_sq_iff_eq_or_eq_neg.mp (τ.injective h3)`.
-/
theorem eq_or_eq_neg_of_purelyImaginary_of_norm_eq :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ξ ξ' : E) (τ : E →+* ℂ),
      cc ξ = -ξ → cc ξ' = -ξ' → ‖τ ξ‖ = ‖τ ξ'‖ → ξ' = ξ ∨ ξ' = -ξ := by
  intro E _ _ _ ξ ξ' τ h h' hn
  have key : ∀ x : E, cc x = -x → τ (x ^ 2) = -((‖τ x‖ ^ 2 : ℝ) : ℂ) := by
    intro x hx
    have h1 : τ (cc x) = (starRingEnd ℂ) (τ x) := IsCMField.complexEmbedding_complexConj E τ x
    rw [hx, map_neg] at h1
    have h2 := Complex.mul_conj' (τ x)
    rw [← h1] at h2
    rw [map_pow]
    push_cast
    linear_combination -h2
  have h3 : τ (ξ' ^ 2) = τ (ξ ^ 2) := by rw [key ξ h, key ξ' h', hn]
  exact sq_eq_sq_iff_eq_or_eq_neg.mp (τ.injective h3)

end GlobalTheory
