import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdmissibleIntegralBasisChangeOne

open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

namespace GlobalTheory.Nef

/- English proof (translation)
Introduce `F _ φ`. Establish `key : ∀ P : F[X], algebraMap (RatFunc F) (LaurentSeries F) (algebraMap F[X] (RatFunc F) P) = algebraMap (PowerSeries F) (LaurentSeries F) (P : PowerSeries F)`. Introduce `P`. Conclude with `(RatFunc.coe_coe P).symm`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨p, q, hq, h⟩`. Use `⟨algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q, ?_⟩` and prove the remaining obligations. Establish `hq' : algebraMap (PowerSeries F) (LaurentSeries F) (q : PowerSeries F) ≠ 0`. Rewrite using `[← key]`. Conclude with `(map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 hq)`.

Rewrite using `[map_div₀, key, key, div_eq_iff hq', ← h, map_mul, mul_comm]`. Introduce and unpack `⟨ρ, h⟩`. Use `⟨ρ.num, ρ.denom, ρ.denom_ne_zero, ?_⟩` and prove the remaining obligations. Apply `HahnSeries.ofPowerSeries_injective (Γ := ℤ)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `algebraMap (PowerSeries F) (LaurentSeries F) _ = algebraMap (PowerSeries F) (LaurentSeries F) _`.

Rewrite using `[map_mul, ← key, ← key, ← h, ← map_mul]`. Use `congr 1`. Establish `hd : algebraMap F[X] (RatFunc F) ρ.denom ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 ρ.denom_ne_zero`. Establish `e : ρ = algebraMap F[X] (RatFunc F) ρ.num / algebraMap F[X] (RatFunc F) ρ.denom` using `(RatFunc.num_div_denom ρ).symm`. Combine the equalities or inequalities in the displayed calculation.
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
