import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Establish `hpow : ϖ ^ i ≠ 0` using `pow_ne_zero _ hϖ.ne_zero`. Establish `h' : (u₂ : R) * ϖ ^ (d + 1) * x = u₁ * y`. Apply `mul_left_cancel₀ hpow` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Establish `hu : IsUnit ((u₁ : R) * y)` using `u₁.isUnit.mul hy`.

Rewrite `hu` using `[← h']`. Conclude with `hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro ((u₂ : R) * ϖ ^ d * x) (by ring)) hu)`.
-/
theorem not_unit_of_pow_succ {R : Type*} [CommRing R] [IsDomain R] {ϖ : R} (hϖ : Irreducible ϖ)
    (u₁ u₂ : Rˣ) (i d : ℕ) {x y : R} (hy : IsUnit y)
    (h : (u₂ : R) * ϖ ^ (i + d + 1) * x = u₁ * ϖ ^ i * y) : False := by
  have hpow : ϖ ^ i ≠ 0 := pow_ne_zero _ hϖ.ne_zero
  have h' : (u₂ : R) * ϖ ^ (d + 1) * x = u₁ * y := by
    apply mul_left_cancel₀ hpow
    calc ϖ ^ i * ((u₂ : R) * ϖ ^ (d + 1) * x) = (u₂ * ϖ ^ (i + d + 1)) * x := by ring
      _ = (u₁ * ϖ ^ i) * y := h
      _ = ϖ ^ i * (u₁ * y) := by ring
  have hu : IsUnit ((u₁ : R) * y) := u₁.isUnit.mul hy
  rw [← h'] at hu
  exact hϖ.not_isUnit (isUnit_of_dvd_unit (Dvd.intro ((u₂ : R) * ϖ ^ d * x) (by ring)) hu)

/- English proof (translation)
Introduce `R F _ _ _ _ _ _ σ p q c ⟨m0, hm0⟩ ⟨m1, hm1⟩ hpq`. Take `⟨a, s, hs, rfl⟩` from `IsFractionRing.div_surjective (A := R) c`. Establish `hs0 : s ≠ 0` using `nonZeroDivisors.ne_zero hs`. Establish `hsF : algebraMap R F s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs`. Establish `key : ∀ m, s * p.coeff m = a * q.coeff m`.

Introduce `m`. Establish `h` using `congrArg (coeff m) hpq`. Rewrite `h` using `[coeff_map, coeff_C_mul, coeff_map]`. Apply `IsFractionRing.injective R F` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, h]`.

Clear the denominators using the available nonvanishing facts. Establish `ha0 : a ≠ 0`. Introduce `ha`. Establish `h` using `key m0`. Rewrite `h` using `[ha, zero_mul]`.

Conclude with `hm0.ne_zero ((mul_eq_zero.mp h).resolve_left hs0)`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible R`. Take `⟨i, u₁, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ`. Take `⟨j, u₂, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ`. Establish `hij : i = j`.

Break down `lt_trichotomy i j with h | h | h` into its components or cases. It suffices to derive a contradiction. Take `⟨d, rfl⟩ : ∃ d, j = i + d + 1` from `⟨j - i - 1, by omega⟩`. Conclude with `not_unit_of_pow_succ hϖ u₁ u₂ i d hm1 (key m1)`. Conclude with `h`.

It suffices to derive a contradiction. Take `⟨d, rfl⟩ : ∃ d, i = j + d + 1` from `⟨i - j - 1, by omega⟩`. Conclude with `not_unit_of_pow_succ hϖ u₂ u₁ j d hm0 (key m0).symm`. Substitute `hij` using the available equality. Use `⟨u₁ * u₂⁻¹, ?_⟩` and prove the remaining obligations.

Rewrite using `[div_eq_iff hsF, ← map_mul]`. Use `congr 1`. Rewrite using `[Units.val_mul, mul_assoc, ← mul_assoc ((u₂⁻¹ : Rˣ) : R), Units.inv_mul, one_mul]`.
-/
theorem PrimitiveUnit.proof : PrimitiveUnit.Statement := by
  intro R F _ _ _ _ _ _ σ p q c ⟨m0, hm0⟩ ⟨m1, hm1⟩ hpq
  obtain ⟨a, s, hs, rfl⟩ := IsFractionRing.div_surjective (A := R) c
  have hs0 : s ≠ 0 := nonZeroDivisors.ne_zero hs
  have hsF : algebraMap R F s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hs
  have key : ∀ m, s * p.coeff m = a * q.coeff m := by
    intro m
    have h := congrArg (coeff m) hpq
    rw [coeff_map, coeff_C_mul, coeff_map] at h
    apply IsFractionRing.injective R F
    rw [map_mul, map_mul, h]
    field_simp
  have ha0 : a ≠ 0 := by
    intro ha
    have h := key m0
    rw [ha, zero_mul] at h
    exact hm0.ne_zero ((mul_eq_zero.mp h).resolve_left hs0)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨i, u₁, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨j, u₂, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hs0 hϖ
  have hij : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, j = i + d + 1 := ⟨j - i - 1, by omega⟩
      exact not_unit_of_pow_succ hϖ u₁ u₂ i d hm1 (key m1)
    · exact h
    · exfalso
      obtain ⟨d, rfl⟩ : ∃ d, i = j + d + 1 := ⟨i - j - 1, by omega⟩
      exact not_unit_of_pow_succ hϖ u₂ u₁ j d hm0 (key m0).symm
  subst hij
  refine ⟨u₁ * u₂⁻¹, ?_⟩
  rw [div_eq_iff hsF, ← map_mul]
  congr 1
  rw [Units.val_mul, mul_assoc, ← mul_assoc ((u₂⁻¹ : Rˣ) : R), Units.inv_mul, one_mul]

end

end GroundTheory.Heights₂.Heights.Vertical
