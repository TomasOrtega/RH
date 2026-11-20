import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `T V _ _ _ _ _ _ _ hinj α ϖ u m k hϖ hu hk h`. Establish `hw : algebraMap T V ϖ ≠ 0`. Introduce `h0`. Apply `hϖ.ne_zero` to reduce the goal to its premises. Apply `hinj` to reduce the goal to its premises.

Rewrite using `[h0, map_zero]`. Establish `hu' : IsUnit (algebraMap T V u)` using `hu.map _`. Establish `hxk : (α ^ m) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k`. Rewrite using `[← pow_mul, h, map_mul, map_pow]`. Establish `hwk : (algebraMap T V ϖ) ^ k ≠ 0` using `pow_ne_zero _ hw`.

Break down `ValuationRing.dvd_total (α ^ m) (algebraMap T V ϖ) with ⟨c, hc⟩ | ⟨c, hc⟩` into its components or cases. Establish `heq : (c ^ k * algebraMap T V u) * (algebraMap T V ϖ) ^ k = 1 * (algebraMap T V ϖ) ^ k`. Combine the equalities or inequalities in the displayed calculation. Establish `h1` using `mul_right_cancel₀ hwk heq`. Establish `hc' : IsUnit c` using `(isUnit_pow_iff hk.ne').mp (IsUnit.of_mul_eq_one _ h1)`.

Take `⟨cu, rfl⟩` from `hc'`. Use `⟨↑cu⁻¹, Units.isUnit _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, mul_comm (α ^ m), ← mul_assoc, Units.inv_mul, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[h1, mul_one]`.

Use `_ = algebraMap T V u := by`. Rewrite using `[← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]`. Establish `heq : c ^ k * (algebraMap T V ϖ) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k`. Rewrite using `[← hxk, hc]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h1` using `mul_right_cancel₀ hwk heq`. Conclude with `⟨c, (isUnit_pow_iff hk.ne').mp (h1 ▸ hu'), by rw [hc, mul_comm], h1⟩`.
-/
theorem dvr_pow_mul_eq_unit_mul_pow_unif :
    ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V], Function.Injective (algebraMap T V) →
    ∀ (α : V) (ϖ u : T) (m k : ℕ), Irreducible ϖ → IsUnit u → 0 < k →
    α ^ (m * k) = algebraMap T V (u * ϖ ^ k) →
    ∃ γ : V, IsUnit γ ∧ α ^ m = γ * algebraMap T V ϖ ∧ γ ^ k = algebraMap T V u := by
  intro T V _ _ _ _ _ _ _ hinj α ϖ u m k hϖ hu hk h
  have hw : algebraMap T V ϖ ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    apply hinj
    rw [h0, map_zero]
  have hu' : IsUnit (algebraMap T V u) := hu.map _
  have hxk : (α ^ m) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k := by
    rw [← pow_mul, h, map_mul, map_pow]
  have hwk : (algebraMap T V ϖ) ^ k ≠ 0 := pow_ne_zero _ hw
  rcases ValuationRing.dvd_total (α ^ m) (algebraMap T V ϖ) with ⟨c, hc⟩ | ⟨c, hc⟩
  ·
    have heq : (c ^ k * algebraMap T V u) * (algebraMap T V ϖ) ^ k = 1 * (algebraMap T V ϖ) ^ k := by
      calc c ^ k * algebraMap T V u * (algebraMap T V ϖ) ^ k
          = c ^ k * (α ^ m) ^ k := by rw [hxk]; ring
        _ = (α ^ m * c) ^ k := by ring
        _ = (algebraMap T V ϖ) ^ k := by rw [← hc]
        _ = 1 * (algebraMap T V ϖ) ^ k := by ring
    have h1 := mul_right_cancel₀ hwk heq
    have hc' : IsUnit c := (isUnit_pow_iff hk.ne').mp (IsUnit.of_mul_eq_one _ h1)
    obtain ⟨cu, rfl⟩ := hc'
    refine ⟨↑cu⁻¹, Units.isUnit _, ?_, ?_⟩
    · rw [hc, mul_comm (α ^ m), ← mul_assoc, Units.inv_mul, one_mul]
    · calc ((↑cu⁻¹ : V)) ^ k = (↑cu⁻¹ : V) ^ k * ((↑cu : V) ^ k * algebraMap T V u) := by
            rw [h1, mul_one]
        _ = algebraMap T V u := by
            rw [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul]
  ·
    have heq : c ^ k * (algebraMap T V ϖ) ^ k = algebraMap T V u * (algebraMap T V ϖ) ^ k := by
      rw [← hxk, hc]; ring
    have h1 := mul_right_cancel₀ hwk heq
    exact ⟨c, (isUnit_pow_iff hk.ne').mp (h1 ▸ hu'), by rw [hc, mul_comm], h1⟩

end GlobalTheory
