import Mathlib
import ReciprocityTheory.GaloisValuations.Global

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

namespace GlobalTheory.InertiaAlmostAll

/- English proof (translation)
Establish `h : IsIntegral B w` using `hw.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h`. Rewrite using `[B.valuation_le_one_iff, ← hy]`. Conclude with `y.2`.
-/
theorem val_le_one_of_isIntegral {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {w : Ω}
    (hw : IsIntegral ℤ w) : B.valuation w ≤ 1 := by
  have h : IsIntegral B w := hw.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
  rw [B.valuation_le_one_iff, ← hy]
  exact y.2

/- English proof (translation)
Use `haveI : Algebra.IsAlgebraic ℤ F := (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).mpr inferInstance`. Use `haveI : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ F Ω`. Take `⟨c, hc, h⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) y).exists_integral_multiple`. Conclude with `⟨c, hc, by simpa [zsmul_eq_mul] using h⟩`.
-/
theorem exists_int_mul (F : Type) {Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (y : Ω) : ∃ c : ℤ, c ≠ 0 ∧ IsIntegral ℤ ((c : Ω) * y) := by
  haveI : Algebra.IsAlgebraic ℤ F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ) (C := F)).mpr inferInstance
  haveI : Algebra.IsAlgebraic ℤ Ω := Algebra.IsAlgebraic.trans ℤ F Ω
  obtain ⟨c, hc, h⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) y).exists_integral_multiple
  exact ⟨c, hc, by simpa [zsmul_eq_mul] using h⟩

/- English proof (translation)
Establish `h : Ideal.span {(c : 𝓞 F)} ≠ 0`. Simplify `hc` using `[Ideal.span_singleton_eq_bot]`. Use `(Ideal.finite_factors h).subset fun v hv => ?_` and prove the remaining obligations. Simplify `hv` using `[Ideal.dvd_span_singleton]`.
-/
theorem finite_mem (F : Type) [Field F] [NumberField F] {c : ℤ} (hc : c ≠ 0) :
    {v : HeightOneSpectrum (𝓞 F) | (c : 𝓞 F) ∈ v.asIdeal}.Finite := by
  have h : Ideal.span {(c : 𝓞 F)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hc
  refine (Ideal.finite_factors h).subset fun v hv => ?_
  simpa [Ideal.dvd_span_singleton] using hv

/- English proof (translation)
Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Take `⟨c₀, hc₀, hx⟩` from `exists_int_mul F x`. Use `set a : Ω := (c₀ : Ω) * x with ha`. Use `choose c hc hci using fun β : Ω => exists_int_mul F (β - a)⁻¹`. Establish `hfin : ((minpoly F a).rootSet Ω).Finite` using `Polynomial.rootSet_finite _ _`.

Use `(hfin.biUnion (t := fun β => {v : HeightOneSpectrum (𝓞 F) | (c β : 𝓞 F) ∈ v.asIdeal}) fun β _ => finite_mem F (hc β)).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨B, hB, τ, hτ, hne⟩`. Establish `hne' : τ a - a ≠ 0`. Rewrite using `[ha, map_mul, map_intCast, ← mul_sub]`. Conclude with `mul_ne_zero (by exact_mod_cast hc₀) (sub_ne_zero.mpr hne)`.

Establish `hint : IsIntegral F a` using `Algebra.IsIntegral.isIntegral a`. Simplify using `only [Set.mem_iUnion, Set.mem_setOf_eq]`. Use `⟨τ a, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Polynomial.mem_rootSet]`. Use `⟨minpoly.ne_zero hint, ?_⟩` and prove the remaining obligations.

Rewrite using `[Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]`. Rewrite using `[← hB]`. Establish `h1` using `hτ.2 a (val_le_one_of_isIntegral B hx)`. Establish `h2` using `val_le_one_of_isIntegral B (hci (τ a))`. Establish `e : algebraMap F Ω (((c (τ a) : ℤ) : 𝓞 F) : F) = ((c (τ a) : Ω) * (τ a - a)⁻¹) * (τ a - a)`.

Rewrite using `[inv_mul_cancel_right₀ hne']`. Simplify using the standard rewrite rules. Rewrite using `[e, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right h2 zero_le h1`.
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
Set `b` to `Module.finBasis F L`. Use `(Set.finite_iUnion fun i => finite_moves F Ω (b i : Ω)).subset ?_` and prove the remaining obligations. Introduce and unpack `v ⟨B, hB, hn⟩`. Assume the negation of the conclusion as `hv`. Apply `hn` to reduce the goal to its premises.

Introduce `τ hτ`. Establish `hb : ∀ i, τ (b i : Ω) = b i`. Introduce `i`. Assume the negation of the conclusion as `h`. Conclude with `hv (Set.mem_iUnion.mpr ⟨i, B, hB, τ, hτ, h⟩)`.

Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`. Establish `: τ.toLinearMap.comp L.val.toLinearMap = L.val.toLinearMap` using `b.ext fun i => by simpa using hb i`. Simplify using `using LinearMap.congr_fun this ⟨y, hy⟩`.
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
