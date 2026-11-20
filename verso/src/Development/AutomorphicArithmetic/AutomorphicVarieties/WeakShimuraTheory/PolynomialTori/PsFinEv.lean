import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.PolynomialTori.FinPow

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

/- English proof (translation)
Introduce `O _ _ B _ _ _ _ h0 t ht ht0 n hn`. Set `ι : ResidueField O →+* B` to `Ideal.Quotient.lift (maximalIdeal O) (algebraMap O B) h0`. Use `letI : UniformSpace (ResidueField O) := ⊥`. Use `letI : WithIdeal B := ⟨maximalIdeal B⟩`. Establish `hadic : IsAdic (maximalIdeal B)` using `rfl`.

Establish `hc : CompleteSpace B ∧ T2Space B` using `hadic.isAdicComplete_iff.mp (IsCO.complete (O := O))`. Use `haveI := hc.1`. Use `haveI := hc.2`. Establish `hcont : Continuous ι` using `continuous_of_discreteTopology`. Establish `hte : PowerSeries.HasEval t` using `by show Filter.Tendsto (fun m => t ^ m) Filter.atTop (nhds 0)`.

Rewrite using `[hadic.hasBasis_nhds_zero.tendsto_right_iff]`. Introduce `i _`. Use `filter_upwards [Filter.eventually_ge_atTop i] with m hm`. Conclude with `Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ht m)`. Set `φ` to `PowerSeries.eval₂Hom hcont hte`.

Establish `hφX : φ PowerSeries.X = t` using `by simp [φ, PowerSeries.coe_eval₂Hom]`. Establish `hφC : ∀ r, φ (PowerSeries.C r) = ι r`. Introduce `r`. Simplify using `[φ, PowerSeries.coe_eval₂Hom]`. Use `⟨φ, ?_, ?_, hφX, fun a => by rw [hφC]; rfl⟩` and prove the remaining obligations.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `f hf`. Assume the negation of the conclusion as `hne`. Establish `hu : IsUnit (PowerSeries.divXPowOrder f)`. Rewrite using `[PowerSeries.isUnit_iff_constantCoeff]`.

Conclude with `Ne.isUnit (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne)`. Establish `h1` using `congrArg φ (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))`. Rewrite `h1` using `[map_mul, map_pow, hφX, hf]`. Conclude with `mul_ne_zero (pow_ne_zero _ ht0) (hu.map φ).ne_zero h1`. Use `letI : Algebra (PowerSeries (ResidueField O)) B := φ.toAlgebra haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField O))) (PowerSeries (ResidueField O)) := by`.

Rewrite using `[PowerSeries.maximalIdeal_eq_span_X]`. Use `infer_instance`. Establish `hmap : Ideal.map (algebraMap (PowerSeries (ResidueField O)) B) (maximalIdeal (PowerSeries (ResidueField O))) = Ideal.span {t}`. Rewrite using `[PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton, RingHom.algebraMap_toAlgebra, hφX]`. Use `show Module.Finite _ _`.

Use `UpperTheory.V.Ws.Po.finPow ?_ ?_ n ?_` and prove the remaining obligations. Rewrite using `[hmap, Ideal.span_le, Set.singleton_subset_iff]`. Conclude with `ht`. Introduce `x`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) x`.

Conclude with `⟨PowerSeries.C (residue O a), by rw [RingHom.algebraMap_toAlgebra, hφC]; exact ha⟩`. Rewrite using `[hmap]`. Conclude with `hn`.
-/
theorem UpperTheory.V.Ws.Po.psFin :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (B : Type) [CommRing B] [Algebra O B] [IsCO O B] [IsDomain B], (∀ a ∈ maximalIdeal O, algebraMap O B a = 0) →
      ∀ t ∈ maximalIdeal B, t ≠ 0 → ∀ n : ℕ, maximalIdeal B ^ n ≤ Ideal.span {t} →
      ∃ φ : PowerSeries (ResidueField O) →+* B, Function.Injective φ ∧ φ.Finite ∧ φ PowerSeries.X = t ∧
        ∀ a : O, φ (PowerSeries.C (residue O a)) = algebraMap O B a := by
  intro O _ _ B _ _ _ _ h0 t ht ht0 n hn
  classical
  let ι : ResidueField O →+* B := Ideal.Quotient.lift (maximalIdeal O) (algebraMap O B) h0
  letI : UniformSpace (ResidueField O) := ⊥
  letI : WithIdeal B := ⟨maximalIdeal B⟩
  have hadic : IsAdic (maximalIdeal B) := rfl
  have hc : CompleteSpace B ∧ T2Space B := hadic.isAdicComplete_iff.mp (IsCO.complete (O := O))
  haveI := hc.1
  haveI := hc.2
  have hcont : Continuous ι := continuous_of_discreteTopology
  have hte : PowerSeries.HasEval t := by
    show Filter.Tendsto (fun m => t ^ m) Filter.atTop (nhds 0)
    rw [hadic.hasBasis_nhds_zero.tendsto_right_iff]
    intro i _
    filter_upwards [Filter.eventually_ge_atTop i] with m hm
    exact Ideal.pow_le_pow_right hm (Ideal.pow_mem_pow ht m)
  let φ := PowerSeries.eval₂Hom hcont hte
  have hφX : φ PowerSeries.X = t := by simp [φ, PowerSeries.coe_eval₂Hom]
  have hφC : ∀ r, φ (PowerSeries.C r) = ι r := by
    intro r
    simp [φ, PowerSeries.coe_eval₂Hom]
  refine ⟨φ, ?_, ?_, hφX, fun a => by rw [hφC]; rfl⟩
  · rw [injective_iff_map_eq_zero]
    intro f hf
    by_contra hne
    have hu : IsUnit (PowerSeries.divXPowOrder f) := by
      rw [PowerSeries.isUnit_iff_constantCoeff]
      exact Ne.isUnit (PowerSeries.constantCoeff_divXPowOrder_eq_zero_iff.not.mpr hne)
    have h1 := congrArg φ (PowerSeries.X_pow_order_mul_divXPowOrder (f := f))
    rw [map_mul, map_pow, hφX, hf] at h1
    exact mul_ne_zero (pow_ne_zero _ ht0) (hu.map φ).ne_zero h1
  · letI : Algebra (PowerSeries (ResidueField O)) B := φ.toAlgebra
    haveI : IsAdicComplete (maximalIdeal (PowerSeries (ResidueField O))) (PowerSeries (ResidueField O)) := by
      rw [PowerSeries.maximalIdeal_eq_span_X]
      infer_instance
    have hmap : Ideal.map (algebraMap (PowerSeries (ResidueField O)) B)
        (maximalIdeal (PowerSeries (ResidueField O))) = Ideal.span {t} := by
      rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.map_span, Set.image_singleton,
        RingHom.algebraMap_toAlgebra, hφX]
    show Module.Finite _ _
    refine UpperTheory.V.Ws.Po.finPow ?_ ?_ n ?_
    · rw [hmap, Ideal.span_le, Set.singleton_subset_iff]
      exact ht
    · intro x
      obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) x
      exact ⟨PowerSeries.C (residue O a), by rw [RingHom.algebraMap_toAlgebra, hφC]; exact ha⟩
    · rw [hmap]
      exact hn
