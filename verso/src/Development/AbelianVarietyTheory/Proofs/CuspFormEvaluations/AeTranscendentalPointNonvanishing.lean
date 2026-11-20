import Mathlib
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero

open MeasureTheory

namespace GlobalTheory

/- English proof (translation)
Establish `: Countable (MvPolynomial ι K)` using `(MvPolynomial.basisMonomials ι K).repr.injective.countable`. Rewrite using `[ae_all_iff]`. Introduce `Q`. Distinguish the cases in `hQ : Q = 0`. Conclude with `Filter.Eventually.of_forall fun t h => absurd hQ h`.

Establish `hm : MvPolynomial.map σ Q ≠ 0`. Introduce `h`. Conclude with `hQ (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))`. Establish `h` using `ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (ι → ℂ)) (LinearEquiv.refl ℂ (ι → ℂ)) _ hm`. Use `filter_upwards [h] with t ht _`.

Rewrite using `[MvPolynomial.eval₂_eq_eval_map]`. Conclude with `ht`.
-/
theorem ae_eval₂_ne_zero_of_countable (K : Type) [Field K] [Countable K] (σ : K →+* ℂ)
    (ι : Type) [Fintype ι] :
    ∀ᵐ t : ι → ℂ, ∀ Q : MvPolynomial ι K, Q ≠ 0 → MvPolynomial.eval₂ σ t Q ≠ 0 := by
  have : Countable (MvPolynomial ι K) :=
    (MvPolynomial.basisMonomials ι K).repr.injective.countable
  rw [ae_all_iff]
  intro Q
  by_cases hQ : Q = 0
  · exact Filter.Eventually.of_forall fun t h => absurd hQ h
  · have hm : MvPolynomial.map σ Q ≠ 0 := by
      intro h
      exact hQ (MvPolynomial.map_injective σ σ.injective (by rw [h, map_zero]))
    have h := ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_linear (volume : Measure (ι → ℂ))
      (LinearEquiv.refl ℂ (ι → ℂ)) _ hm
    filter_upwards [h] with t ht _
    rw [MvPolynomial.eval₂_eq_eval_map]
    exact ht

end GlobalTheory
