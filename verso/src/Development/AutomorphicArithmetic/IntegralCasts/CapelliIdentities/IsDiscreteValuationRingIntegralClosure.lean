import Mathlib

open Polynomial

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.
-/
private theorem isIntegral_of_spectralNorm_le_one (l : ℕ) [Fact l.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L]
    [IsScalarTower ℤ_[l] ℚ_[l] L] (x : L) (hx : spectralNorm ℚ_[l] L x ≤ 1) :
    IsIntegral ℤ_[l] x := by
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have hm : (minpoly ℚ_[l] x).Monic := minpoly.monic hint
  have hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1 := (spectralValue_le_one_iff hm).mp hx
  have hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, hc n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]

/- English proof (translation)
Consider separately whether the proposition holds or fails. Prove the first alternative. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Establish an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. A detailed English derivation is pending.
-/
private theorem isIntegral_or_isIntegral_inv (l : ℕ) [Fact l.Prime] (L : Type*) [Field L]
    [Algebra ℚ_[l] L] [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L]
    [IsScalarTower ℤ_[l] ℚ_[l] L] (x : L) :
    IsIntegral ℤ_[l] x ∨ IsIntegral ℤ_[l] x⁻¹ := by
  by_cases hx : spectralNorm ℚ_[l] L x ≤ 1
  · exact Or.inl (isIntegral_of_spectralNorm_le_one l L x hx)
  · refine Or.inr (isIntegral_of_spectralNorm_le_one l L x⁻¹ ?_)
    have hx1 : 1 < spectralNorm ℚ_[l] L x := not_le.mp hx
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [spectralNorm_zero] at hx1
      exact absurd hx1 (by norm_num)
    have hmul : spectralNorm ℚ_[l] L x * spectralNorm ℚ_[l] L x⁻¹ = 1 := by
      have h := spectralAlgNorm_mul (K := ℚ_[l]) (L := L) x x⁻¹
      rw [mul_inv_cancel₀ hx0, spectralAlgNorm_one] at h
      exact h.symm
    have h0 : 0 ≤ spectralNorm ℚ_[l] L x⁻¹ := spectralNorm_nonneg _
    nlinarith

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. A detailed English derivation is pending.
-/
private theorem isDiscreteValuationRing_integralClosure (l : ℕ) [Fact l.Prime] (L : Type*) [Field L] [Algebra ℚ_[l] L]
    [FiniteDimensional ℚ_[l] L] [Algebra ℤ_[l] L] [IsScalarTower ℤ_[l] ℚ_[l] L] :
    IsDiscreteValuationRing (integralClosure ℤ_[l] L) := by
  have hD : IsDedekindDomain (integralClosure ℤ_[l] L) :=
    integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] L
  have hF : IsFractionRing (integralClosure ℤ_[l] L) L :=
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] L
  have hV : ValuationRing (integralClosure ℤ_[l] L) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ L]
    intro x
    rcases isIntegral_or_isIntegral_inv l L x with h | h
    · exact Or.inl ⟨⟨x, h⟩, rfl⟩
    · exact Or.inr ⟨⟨x⁻¹, h⟩, rfl⟩
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] L)) := by
    intro a b hab
    have h : algebraMap ℤ_[l] L a = algebraMap ℤ_[l] L b :=
      congrArg (fun z : integralClosure ℤ_[l] L => (z : L)) hab
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L b]
      at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] L).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] L) := fun h =>
    IsDiscreteValuationRing.not_isField ℤ_[l] (isField_of_isIntegral_of_isField hinj h)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] L) hnf).out 0 1).mpr hV

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. A detailed English derivation is pending.
-/
theorem UpperTheory.integralClosure_isDVR :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] ↥K], IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥K) := by
  intro l _ K _
  exact isDiscreteValuationRing_integralClosure l K
