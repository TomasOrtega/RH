import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift

open MeasureTheory GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

namespace GlobalTheory.AutomorphicL2Local

/- English proof (translation)
Use `set T : Set Γ := {γ | (γ : G) * x ∈ C} with hT`. Establish `h1 : (fun γ : Γ => C.indicator (fun _ => a) ((γ : G) * x)) = T.indicator (fun _ => a)`. Use extensionality with `γ`. Simplify using `[T, Set.indicator_apply]`. Rewrite using `[h1, ← tsum_subtype T (fun _ => a), ENNReal.tsum_set_const]`.

Establish `hle : T.encard ≤ {γ : Γ | (γ : G) ∈ C * C⁻¹}.encard`. Break down `T.eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩` into its components or cases. Simplify using `[h]`. Combine the equalities or inequalities in the displayed calculation. Use `Set.encard_le_encard ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨γ, hγ, rfl⟩`. Use `Set.mem_mul.mpr ⟨(γ : G) * x, hγ, ((γ₀ : G) * x)⁻¹, by simpa [hT] using hγ₀, ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`. Conclude with `mul_le_mul_of_nonneg_right (by exact_mod_cast hle) bot_le`.
-/
theorem tsum_indicator_le {G : Type*} [Group G] (Γ : Subgroup G) (C : Set G) (x : G) (a : ℝ≥0∞) :
    ∑' γ : Γ, C.indicator (fun _ => a) (γ * x) ≤ ({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℝ≥0∞) * a := by
  classical
  set T : Set Γ := {γ | (γ : G) * x ∈ C} with hT
  have h1 : (fun γ : Γ => C.indicator (fun _ => a) ((γ : G) * x)) = T.indicator (fun _ => a) := by
    ext γ
    simp [T, Set.indicator_apply]
  rw [h1, ← tsum_subtype T (fun _ => a), ENNReal.tsum_set_const]
  have hle : T.encard ≤ {γ : Γ | (γ : G) ∈ C * C⁻¹}.encard := by
    rcases T.eq_empty_or_nonempty with h | ⟨γ₀, hγ₀⟩
    · simp [h]
    calc T.encard = ((fun γ => γ * γ₀⁻¹) '' T).encard :=
          (Set.InjOn.encard_image (s := T) (f := fun γ : Γ => γ * γ₀⁻¹)
            (fun _ _ _ _ h => mul_right_cancel h)).symm
      _ ≤ _ := by
          refine Set.encard_le_encard ?_
          rintro _ ⟨γ, hγ, rfl⟩
          refine Set.mem_mul.mpr ⟨(γ : G) * x, hγ, ((γ₀ : G) * x)⁻¹, by simpa [hT] using hγ₀, ?_⟩
          simp [mul_assoc]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) bot_le

/- English proof (translation)
Introduce `G _ _ _ _ _ _ _ _ Γ _ μ _ _ F C hC`. Establish `hmeas : AEStronglyMeasurable (lift Γ F) μ` using `aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)`. Establish `hCm : MeasurableSet C` using `hC.isClosed.measurableSet`. Use `set N : ℝ≥0∞ := (({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℕ∞) : ℝ≥0∞) with hNdef`. Establish `hN : N ≠ ⊤`.

Establish `hfin : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite` using `finite_mem_compact (Γ := Γ) (hC.mul hC.inv)`. Simplify `hfin.encard_lt_top.ne` using `[N]`. Establish `hF2 : ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ < ∞`. Use `(Lp.memLp F).eLpNorm_lt_top` as an intermediate fact. Rewrite `this` using `[eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]`.

Simplify using `using this`. Establish `key : ∫⁻ g, ‖lift Γ F g‖ₑ ^ (2 : ℝ) ∂μ.restrict C < ∞`. Rewrite using `[← lintegral_indicator hCm, lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeas.enorm.pow_const (2 : ℝ)).indicator hCm)]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun q => ?_` and prove the remaining obligations.

Establish `e : ∀ γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out) = C.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) (γ * q.out)`. Introduce `γ`. Simplify using `only [Set.indicator_apply]`. Use `split_ifs`. Simplify using `[lift, mk_mul, Quotient.out_eq]`.

Both sides reduce to the same expression. Repeatedly rewrite using `[e]`. Conclude with `tsum_indicator_le Γ C q.out _`. Use `_ = N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ := lintegral_const_mul' _ _ hN`. Use `_ < ∞ := ENNReal.mul_lt_top hN.lt_top hF2`.

Establish `hLp : MemLp (lift Γ F) 2 (μ.restrict C)`. Use `⟨hmeas.restrict, ?_⟩` and prove the remaining obligations. Rewrite using `[eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]`. Simplify using `using key`. Use `⟨hLp, ?_⟩` and prove the remaining obligations.

Establish `: IsFiniteMeasure (μ.restrict C)` using `isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne`. Conclude with `hLp.integrable one_le_two`.
-/
theorem memLp_restrict_compact : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [DiscreteTopology Γ] (μ : Measure G) [μ.IsHaarMeasure] [μ.IsMulRightInvariant], ∀ (F : L2 Γ μ) (C : Set G), IsCompact C → MemLp (lift Γ F) 2 (μ.restrict C) ∧ IntegrableOn (lift Γ F) C μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ μ _ _ F C hC
  classical
  have hmeas : AEStronglyMeasurable (lift Γ F) μ :=
    aestronglyMeasurable_quotMeasure_iff_lift.mp (Lp.aestronglyMeasurable F)
  have hCm : MeasurableSet C := hC.isClosed.measurableSet
  set N : ℝ≥0∞ := (({γ : Γ | (γ : G) ∈ C * C⁻¹}.encard : ℕ∞) : ℝ≥0∞) with hNdef
  have hN : N ≠ ⊤ := by
    have hfin : {γ : Γ | (γ : G) ∈ C * C⁻¹}.Finite := finite_mem_compact (Γ := Γ) (hC.mul hC.inv)
    simpa [N] using hfin.encard_lt_top.ne
  have hF2 : ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ < ∞ := by
    have := (Lp.memLp F).eLpNorm_lt_top
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top] at this
    simpa using this
  have key : ∫⁻ g, ‖lift Γ F g‖ₑ ^ (2 : ℝ) ∂μ.restrict C < ∞ := by
    rw [← lintegral_indicator hCm,
      lintegral_eq_lintegral_tsum (Γ := Γ) ((hmeas.enorm.pow_const (2 : ℝ)).indicator hCm)]
    calc ∫⁻ q, ∑' γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out) ∂quotMeasure Γ μ
        ≤ ∫⁻ q, N * ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ := by
          refine lintegral_mono fun q => ?_
          have e : ∀ γ : Γ, C.indicator (fun g => ‖lift Γ F g‖ₑ ^ (2 : ℝ)) (γ * q.out)
              = C.indicator (fun _ => ‖F q‖ₑ ^ (2 : ℝ)) (γ * q.out) := by
            intro γ
            simp only [Set.indicator_apply]
            split_ifs
            · simp [lift, mk_mul, Quotient.out_eq]
            · rfl
          simp_rw [e]
          exact tsum_indicator_le Γ C q.out _
      _ = N * ∫⁻ q, ‖F q‖ₑ ^ (2 : ℝ) ∂quotMeasure Γ μ := lintegral_const_mul' _ _ hN
      _ < ∞ := ENNReal.mul_lt_top hN.lt_top hF2
  have hLp : MemLp (lift Γ F) 2 (μ.restrict C) := by
    refine ⟨hmeas.restrict, ?_⟩
    rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top two_ne_zero ENNReal.ofNat_ne_top]
    simpa using key
  refine ⟨hLp, ?_⟩
  have : IsFiniteMeasure (μ.restrict C) := isFiniteMeasure_restrict.mpr hC.measure_lt_top.ne
  exact hLp.integrable one_le_two

end GlobalTheory.AutomorphicL2Local
