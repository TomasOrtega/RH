import Mathlib

open Polynomial

/- English proof (translation)
Establish `hint : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `hm : (minpoly ℚ_[l] x).Monic` using `minpoly.monic hint`. Establish `hc : ∀ n, ‖(minpoly ℚ_[l] x).coeff n‖ ≤ 1` using `(spectralValue_le_one_iff hm).mp hx`. Establish `hl : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`.

Introduce `n`. Conclude with `⟨⟨_, hc n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl hm`. Use `⟨q, hqm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]`.
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
Distinguish the cases in `hx : spectralNorm ℚ_[l] L x ≤ 1`. Conclude with `Or.inl (isIntegral_of_spectralNorm_le_one l L x hx)`. Use `Or.inr (isIntegral_of_spectralNorm_le_one l L x⁻¹ ?_)` and prove the remaining obligations. Establish `hx1 : 1 < spectralNorm ℚ_[l] L x` using `not_le.mp hx`. Establish `hx0 : x ≠ 0`.

Introduce and unpack `rfl`. Rewrite `hx1` using `[spectralNorm_zero]`. Conclude with `absurd hx1 (by norm_num)`. Establish `hmul : spectralNorm ℚ_[l] L x * spectralNorm ℚ_[l] L x⁻¹ = 1`. Establish `h` using `spectralAlgNorm_mul (K := ℚ_[l]) (L := L) x x⁻¹`.

Rewrite `h` using `[mul_inv_cancel₀ hx0, spectralAlgNorm_one]`. Conclude with `h.symm`. Establish `h0 : 0 ≤ spectralNorm ℚ_[l] L x⁻¹` using `spectralNorm_nonneg _`. Use the polynomial consequences of the given equalities and inequalities.
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
Establish `hD : IsDedekindDomain (integralClosure ℤ_[l] L)` using `integralClosure.isDedekindDomain ℤ_[l] ℚ_[l] L`. Establish `hF : IsFractionRing (integralClosure ℤ_[l] L) L` using `integralClosure.isFractionRing_of_finite_extension ℚ_[l] L`. Establish `hV : ValuationRing (integralClosure ℤ_[l] L)`. Rewrite using `[ValuationRing.iff_isInteger_or_isInteger _ L]`. Introduce `x`.

Break down `isIntegral_or_isIntegral_inv l L x with h | h` into its components or cases. Conclude with `Or.inl ⟨⟨x, h⟩, rfl⟩`. Conclude with `Or.inr ⟨⟨x⁻¹, h⟩, rfl⟩`. Establish `hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] L))`. Introduce `a b hab`.

Establish `h : algebraMap ℤ_[l] L a = algebraMap ℤ_[l] L b` using `congrArg (fun z : integralClosure ℤ_[l] L => (z : L)) hab`. Rewrite `h` using `[IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] L b]`. Conclude with `IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] L).injective h)`. Establish `hnf : ¬ IsField (integralClosure ℤ_[l] L)` using `fun h => IsDiscreteValuationRing.not_isField ℤ_[l] (isField_of_isIntegral_of_isField hinj h)`. Conclude with `((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] L) hnf).out 0 1).mpr hV`.
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
Introduce `l _ K _`. Conclude with `isDiscreteValuationRing_integralClosure l K`.
-/
theorem UpperTheory.integralClosure_isDVR :
    ∀ {l : ℕ} [Fact (Nat.Prime l)] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] ↥K], IsDiscreteValuationRing ↥(integralClosure ℤ_[l] ↥K) := by
  intro l _ K _
  exact isDiscreteValuationRing_integralClosure l K
