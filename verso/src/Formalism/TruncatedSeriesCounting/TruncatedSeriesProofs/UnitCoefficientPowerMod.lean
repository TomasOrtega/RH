import Mathlib
import Formalism.TruncatedSeriesCounting.StatementX

noncomputable section

namespace Formalism.TruncatedSeriesCounting.X

open PowerSeries

/- English proof (translation)
Introduce `O _ ℓ ε u y`. Establish `hsplit : ∃ W : PowerSeries O, (Formalism.WindowSums.p1 ℓ ε u) ^ y = (u * X ^ ℓ) ^ y + C (ℓ : O) * W`. Take `⟨V, hV⟩` from `sub_dvd_pow_sub_pow (Formalism.WindowSums.p1 ℓ ε u) (u * X ^ ℓ) y`. Use `⟨ε * V, ?_⟩` and prove the remaining obligations. Establish `: Formalism.WindowSums.p1 ℓ ε u - u * X ^ ℓ = C (ℓ : O) * ε` using `by unfold Formalism.WindowSums.p1; ring`.

Rewrite `hV` using `[this]`. Take the linear combination `hV`. Take `⟨W, hW⟩` from `hsplit`. Establish `hc : coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) = constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W`. Rewrite using `[hW, map_add, coeff_C_mul, mul_pow, ← pow_mul, mul_comm ℓ y]`.

Use `coeff_mul_X_pow (u ^ y) (y * ℓ) 0` as an intermediate fact. Rewrite `this` using `[zero_add]`. Rewrite using `[this, coeff_zero_eq_constantCoeff, map_pow]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hc, add_sub_cancel_left, Ideal.mem_span_singleton]`.

Conclude with `dvd_mul_right _ _`. Introduce `hloc hℓ hu`. Rewrite using `[hc]`. Establish `h0 : IsUnit (constantCoeff u ^ y)` using `(hu.map constantCoeff).pow y`. Establish `h1 : (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O` using `Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hℓ)`.

Assume the negation of the conclusion as `hne`. Establish `h2 : constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).mpr hne`. Establish `h3` using `Ideal.sub_mem _ h2 h1`. Rewrite `h3` using `[add_sub_cancel_right]`. Conclude with `((IsLocalRing.mem_maximalIdeal _).mp h3) h0`.
-/
theorem unit_coefficient_power_mod : UnitCoefficientPowerMod := by
  intro O _ ℓ ε u y
  have hsplit : ∃ W : PowerSeries O,
      (Formalism.WindowSums.p1 ℓ ε u) ^ y = (u * X ^ ℓ) ^ y + C (ℓ : O) * W := by
    obtain ⟨V, hV⟩ := sub_dvd_pow_sub_pow (Formalism.WindowSums.p1 ℓ ε u) (u * X ^ ℓ) y
    refine ⟨ε * V, ?_⟩
    have : Formalism.WindowSums.p1 ℓ ε u - u * X ^ ℓ = C (ℓ : O) * ε := by unfold Formalism.WindowSums.p1; ring
    rw [this] at hV
    linear_combination hV
  obtain ⟨W, hW⟩ := hsplit
  have hc : coeff (ℓ * y) ((Formalism.WindowSums.p1 ℓ ε u) ^ y) =
      constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W := by
    rw [hW, map_add, coeff_C_mul, mul_pow, ← pow_mul, mul_comm ℓ y]
    have := coeff_mul_X_pow (u ^ y) (y * ℓ) 0
    rw [zero_add] at this
    rw [this, coeff_zero_eq_constantCoeff, map_pow]
  refine ⟨?_, ?_⟩
  · rw [hc, add_sub_cancel_left, Ideal.mem_span_singleton]; exact dvd_mul_right _ _
  · intro hloc hℓ hu
    rw [hc]
    have h0 : IsUnit (constantCoeff u ^ y) := (hu.map constantCoeff).pow y
    have h1 : (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      Ideal.mul_mem_right _ _ ((IsLocalRing.mem_maximalIdeal _).mpr hℓ)
    by_contra hne
    have h2 : constantCoeff u ^ y + (ℓ : O) * coeff (ℓ * y) W ∈ IsLocalRing.maximalIdeal O :=
      (IsLocalRing.mem_maximalIdeal _).mpr hne
    have h3 := Ideal.sub_mem _ h2 h1
    rw [add_sub_cancel_right] at h3
    exact ((IsLocalRing.mem_maximalIdeal _).mp h3) h0

end Formalism.TruncatedSeriesCounting.X
