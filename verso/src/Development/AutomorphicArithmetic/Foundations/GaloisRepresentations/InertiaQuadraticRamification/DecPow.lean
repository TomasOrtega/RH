import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertiaGenAlt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsCoprimePowOfMemIneKer

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.TameQuot

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ A t hA p hp hpt ζ hζ`. Establish `hN : ¬ A.valuation (p : Ω) < 1`. Simplify using `using not_valuation_lt_one_of_isPlaceOver hpt hA 1`. Establish `hz1 : ζ ^ p = 1` using `hζ.pow_eq_one`. Establish `hint : ζ ∈ IntCl F Ω` using `IsIntegral.of_pow hp.pos (by rw [hz1]; exact isIntegral_one)`.

Establish `hv : A.valuation ζ ≤ 1`. Establish `h1 : A.valuation ζ ^ p = 1` using `by rw [← map_pow, hz1, map_one]`. Conclude with `((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le`. Use `⟨fun g hg => ?_, fun τ hτ => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `exists_pow_cong hA hg {⟨ζ, hint⟩}`.

Use `⟨i, eq_of_pow_eq_one A hN ?_ ?_ (hi ⟨ζ, hint⟩ (Finset.mem_singleton_self _))⟩` and prove the remaining obligations. Rewrite using `[← map_pow, hz1, map_one]`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hz1, one_pow]`. Conclude with `eq_of_pow_eq_one A hN (by rw [← map_pow, hz1, map_one]) hz1 ((mem_Ine.1 hτ).2 ζ hv)`.
-/
theorem decPow : DecPow := by
  intro F Ω _ _ _ _ _ A t hA p hp hpt ζ hζ
  have hN : ¬ A.valuation (p : Ω) < 1 := by
    simpa using not_valuation_lt_one_of_isPlaceOver hpt hA 1
  have hz1 : ζ ^ p = 1 := hζ.pow_eq_one
  have hint : ζ ∈ IntCl F Ω :=
    IsIntegral.of_pow hp.pos (by rw [hz1]; exact isIntegral_one)
  have hv : A.valuation ζ ≤ 1 := by
    have h1 : A.valuation ζ ^ p = 1 := by rw [← map_pow, hz1, map_one]
    exact ((pow_eq_one_iff.1 h1).resolve_right hp.ne_zero).le
  refine ⟨fun g hg => ?_, fun τ hτ => ?_⟩
  · obtain ⟨i, hi⟩ := exists_pow_cong hA hg {⟨ζ, hint⟩}
    refine ⟨i, eq_of_pow_eq_one A hN ?_ ?_ (hi ⟨ζ, hint⟩ (Finset.mem_singleton_self _))⟩
    · rw [← map_pow, hz1, map_one]
    · rw [← pow_mul, mul_comm, pow_mul, hz1, one_pow]
  · exact eq_of_pow_eq_one A hN (by rw [← map_pow, hz1, map_one]) hz1 ((mem_Ine.1 hτ).2 ζ hv)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
