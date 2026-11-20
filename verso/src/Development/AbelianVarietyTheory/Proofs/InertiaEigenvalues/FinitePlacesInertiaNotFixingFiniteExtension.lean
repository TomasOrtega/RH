import Mathlib
import ReciprocityTheory.GaloisValuations.Global

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.InertiaAlmostAll

/- English proof (translation)
Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem val_le_one_of_isIntegral {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {w : Ω}
    (hw : IsIntegral ℤ w) : B.valuation w ≤ 1 := by
  have h : IsIntegral B w := hw.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [B.valuation_le_one_iff, ← hy]
  exact y.2

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem exists_int_mul (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (y : Ω) : ∃ c : ℤ, c ≠ 0 ∧ IsIntegral ℤ ((c : Ω) * y) := by
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).mpr inferInstance
  haveI : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ F Ω
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) y).exists_integral_multiple
  exact ⟨c, hc, by simpa [zsmul_eq_mul] using h⟩

/- English proof (translation)
Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts.
-/
theorem finite_mem (F : Type) [Field F] [NumberField F] {c : ℤ} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | (c : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {(c : 𝓞 F)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hc
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem finite_moves (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (x : Ω) :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ∃ τ ∈ Ine (F := F) B, τ x ≠ x}.Finite := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨c₀, hc₀, hx⟩ := exists_int_mul F x
  set a : Ω := (c₀ : Ω) * x with ha
  choose c hc hci using fun β : Ω => exists_int_mul F (β - a)⁻¹
  have hfin : ((minpoly F a).rootSet Ω).Finite := Polynomial.rootSet_finite _ _
  refine (hfin.biUnion (t := fun β => {v : HeightOneSpectrum (𝓞 F) | (c β : 𝓞 F) ∈ v.asIdeal})
    fun β _ => finite_mem F (hc β)).subset ?_
  rintro v ⟨B, hB, τ, hτ, hne⟩
  have hne' : τ a - a ≠ 0 := by
    rw [ha, map_mul, map_intCast, ← mul_sub]
    exact mul_ne_zero (by exact_mod_cast hc₀) (sub_ne_zero.mpr hne)
  have hint : IsIntegral F a := Algebra.IsIntegral.isIntegral a
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  refine ⟨τ a, ?_, ?_⟩
  · rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hint, ?_⟩
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  · rw [← hB]
    have h1 := hτ.2 a (val_le_one_of_isIntegral B hx)
    have h2 := val_le_one_of_isIntegral B (hci (τ a))
    have e : algebraMap F Ω (((c (τ a) : ℤ) : 𝓞 F) : F)
        = ((c (τ a) : Ω) * (τ a - a)⁻¹) * (τ a - a) := by
      rw [inv_mul_cancel_right₀ hne']
      simp
    rw [e, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right h2 zero_le h1

/- English proof (translation)
Introduce a local definition for the expression. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Assume the negation of the conclusion and derive a contradiction. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem finite_ramified (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (L : IntermediateField F Ω) [FiniteDimensional F L] :
    {v : HeightOneSpectrum (𝓞 F) | ∃ B : ValuationSubring Ω, IsPlaceOver B v ∧
      ¬ Ine (F := F) B ≤ L.fixingSubgroup}.Finite := by
  let b := Module.finBasis F L
  refine (Set.finite_iUnion fun i => finite_moves F Ω (b i : Ω)).subset ?_
  rintro v ⟨B, hB, hn⟩
  by_contra hv
  apply hn
  intro τ hτ
  have hb : ∀ i, τ (b i : Ω) = b i := by
    intro i
    by_contra h
    exact hv (Set.mem_iUnion.mpr ⟨i, B, hB, τ, hτ, h⟩)
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have : τ.toLinearMap.comp L.val.toLinearMap = L.val.toLinearMap :=
    b.ext fun i => by simpa using hb i
  simpa using LinearMap.congr_fun this ⟨y, hy⟩

end GlobalTheory.InertiaAlmostAll
