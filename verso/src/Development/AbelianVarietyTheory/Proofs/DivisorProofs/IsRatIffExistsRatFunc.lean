import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Assume the hypotheses and unpack their components.

Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Establish an intermediate fact. Chain the equalities or inequalities of the calculation. A detailed English derivation is pending.
-/
theorem isRat_iff_exists_ratFunc : ∀ (F : Type) [Field F] (φ : PowerSeries F), IsRat φ ↔
    ∃ ρ : RatFunc F, algebraMap (RatFunc F) (LaurentSeries F) ρ = algebraMap (PowerSeries F) (LaurentSeries F) φ := by
  intro F _ φ
  have key : ∀ P : F[X], algebraMap (RatFunc F) (LaurentSeries F) (algebraMap F[X] (RatFunc F) P) =
      algebraMap (PowerSeries F) (LaurentSeries F) (P : PowerSeries F) := by
    intro P
    exact (RatFunc.coe_coe P).symm
  constructor
  · rintro ⟨p, q, hq, h⟩
    refine ⟨algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q, ?_⟩
    have hq' : algebraMap (PowerSeries F) (LaurentSeries F) (q : PowerSeries F) ≠ 0 := by
      rw [← key]
      exact (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 hq)
    rw [map_div₀, key, key, div_eq_iff hq', ← h, map_mul, mul_comm]
  · rintro ⟨ρ, h⟩
    refine ⟨ρ.num, ρ.denom, ρ.denom_ne_zero, ?_⟩
    apply HahnSeries.ofPowerSeries_injective (Γ := ℤ)
    change algebraMap (PowerSeries F) (LaurentSeries F) _ = algebraMap (PowerSeries F) (LaurentSeries F) _
    rw [map_mul, ← key, ← key, ← h, ← map_mul]
    congr 1
    have hd : algebraMap F[X] (RatFunc F) ρ.denom ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 ρ.denom_ne_zero
    have e : ρ = algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom :=
      (RatFunc.num_div_denom ρ).symm
    calc algebraMap F[X] (RatFunc F) ρ.denom * ρ
        = algebraMap F[X] (RatFunc F) ρ.denom *
            (algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom) := congrArg _ e
      _ = algebraMap F[X] (RatFunc F) ρ.num := mul_div_cancel₀ _ hd

end GlobalTheory.Nef
