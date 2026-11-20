import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.IsCharOneOfSubsingleton

open PowerSeries IsLocalRing UpperTheory.V.abelian₂
open IsDiscreteValuationRing (addVal)
open scoped Pointwise TensorProduct Topology

/- English proof (translation)
Establish `hi : IsIntegral ℚ_[l] x` using `Algebra.IsIntegral.isIntegral x`. Establish `h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x))` using `rfl`. Rewrite using `[h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]`. Prove the components needed by the constructor for the conclusion. Introduce `h n`.

Rewrite using `[minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]`. Conclude with `PadicInt.norm_le_one _`. Introduce `h`. Establish `hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l])` using `(Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩`. Take `⟨q, hq, -, hqm⟩` from `Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)`.

Conclude with `⟨q, hqm, by`. Rewrite using `[← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩`.
-/
private theorem UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K]
    (φ : K →ₐ[ℚ_[l]] PadicAlgCl l) (x : K) : IsIntegral ℤ_[l] x ↔ ‖φ x‖ ≤ 1 := by
  have hi : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
  have h0 : ‖φ x‖ = spectralValue (minpoly ℚ_[l] (φ x)) := rfl
  rw [h0, minpoly.algHom_eq φ φ.injective, spectralValue_le_one_iff (minpoly.monic hi)]
  constructor
  · intro h n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  · intro h
    have hl' : minpoly ℚ_[l] x ∈ Polynomial.lifts (algebraMap ℤ_[l] ℚ_[l]) :=
      (Polynomial.lifts_iff_coeff_lifts _).mpr fun n => ⟨⟨_, h n⟩, rfl⟩
    obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl' (minpoly.monic hi)
    exact ⟨q, hqm, by
      rw [← Polynomial.aeval_def, ← Polynomial.aeval_map_algebraMap ℚ_[l], hq, minpoly.aeval]⟩

/- English proof (translation)
Introduce `l hl K _ _ _ _ _`. Set `φ : K →ₐ[ℚ_[l]] PadicAlgCl l` to `IsAlgClosed.lift`. Establish `hint` using `UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis φ`. Establish `hunit : ∀ a : integralClosure ℤ_[l] K, ‖φ a‖ = 1 → IsUnit a`. Introduce `a ha`.

Establish `h0 : (a : K) ≠ 0`. Introduce `h`. Rewrite `ha` using `[h]`. Simplify using `at ha`. Establish `hi : IsIntegral ℤ_[l] (a : K)⁻¹`.

Rewrite using `[hint, map_inv₀, norm_inv, ha, inv_one]`. Conclude with `IsUnit.of_mul_eq_one (⟨_, hi⟩ : integralClosure ℤ_[l] K) (Subtype.ext (mul_inv_cancel₀ h0))`. Establish `hloc : IsLocalRing (integralClosure ℤ_[l] K)`. Use `IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_` and prove the remaining obligations. Establish `ha : ‖φ a‖ ≤ 1` using `(hint _).1 a.2`.

Break down `ha.eq_or_lt with h | h` into its components or cases. Conclude with `Or.inl (hunit a h)`. Use `Or.inr (hunit _ (le_antisymm ((hint _).1 (1 - a).2) ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Establish `h1 : φ ((1 - a : integralClosure ℤ_[l] K) : K) + φ a = 1` using `by simp`. Establish `h2` using `(PadicAlgCl.isNonarchimedean l _ _).trans_lt (max_lt hlt h)`. Simplify using `only [h1] at h2`. Simplify using `at h2`. Establish `hded : IsDedekindDomain (integralClosure ℤ_[l] K)` using `IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)`.

Establish `hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K))`. Introduce `a b hab`. Establish `h` using `congrArg (fun x : integralClosure ℤ_[l] K => (x : K)) hab`. Simplify using `only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K] at h`. Conclude with `IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] K).injective h)`.

Establish `hnf : ¬ IsField (integralClosure ℤ_[l] K)` using `fun hf => IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)`. Conclude with `⟨((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded, IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K), integralClosure.isFractionRing_of_finite_extension ℚ_[l] K⟩`.
-/
theorem UpperTheory.V.abelian₂.dvr_intClosure :
    ∀ (l : ℕ) [Fact l.Prime] (K : Type) [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
      [FiniteDimensional ℚ_[l] K],
      IsDiscreteValuationRing (integralClosure ℤ_[l] K) ∧ Module.Finite ℤ_[l] (integralClosure ℤ_[l] K) ∧
        IsFractionRing (integralClosure ℤ_[l] K) K := by
  intro l hl K _ _ _ _ _
  let φ : K →ₐ[ℚ_[l]] PadicAlgCl l := IsAlgClosed.lift
  have hint := UpperTheory.V.abelian₂.isIntegral_iff_norm_le_one_bis φ
  have hunit : ∀ a : integralClosure ℤ_[l] K, ‖φ a‖ = 1 → IsUnit a := by
    intro a ha
    have h0 : (a : K) ≠ 0 := by
      intro h
      rw [h] at ha
      simp at ha
    have hi : IsIntegral ℤ_[l] (a : K)⁻¹ := by
      rw [hint, map_inv₀, norm_inv, ha, inv_one]
    exact IsUnit.of_mul_eq_one (⟨_, hi⟩ : integralClosure ℤ_[l] K) (Subtype.ext (mul_inv_cancel₀ h0))
  have hloc : IsLocalRing (integralClosure ℤ_[l] K) := by
    refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
    have ha : ‖φ a‖ ≤ 1 := (hint _).1 a.2
    rcases ha.eq_or_lt with h | h
    · exact Or.inl (hunit a h)
    · refine Or.inr (hunit _ (le_antisymm ((hint _).1 (1 - a).2) ?_))
      by_contra hlt
      push Not at hlt
      have h1 : φ ((1 - a : integralClosure ℤ_[l] K) : K) + φ a = 1 := by simp
      have h2 := (PadicAlgCl.isNonarchimedean l _ _).trans_lt (max_lt hlt h)
      simp only [h1] at h2
      simp at h2
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K)
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    have h := congrArg (fun x : integralClosure ℤ_[l] K => (x : K)) hab
    simp only [Subalgebra.coe_algebraMap, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] K] at h
    exact IsFractionRing.injective ℤ_[l] ℚ_[l] ((algebraMap ℚ_[l] K).injective h)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l] ((Algebra.IsIntegral.isField_iff_isField hinj).2 hf)
  exact ⟨((IsDiscreteValuationRing.TFAE _ hnf).out 0 2).mpr hded,
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] K (integralClosure ℤ_[l] K),
    integralClosure.isFractionRing_of_finite_extension ℚ_[l] K⟩
