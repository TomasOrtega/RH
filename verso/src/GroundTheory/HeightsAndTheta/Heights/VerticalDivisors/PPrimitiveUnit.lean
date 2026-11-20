import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial

noncomputable section

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result. Chain the equalities or inequalities of the calculation. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Separate the alternatives or extract the components of the hypothesis.

It suffices to derive a contradiction. Extract witnesses or component facts from the available result. It suffices to derive a contradiction. Extract witnesses or component facts from the available result. Substitute using the available equality.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
