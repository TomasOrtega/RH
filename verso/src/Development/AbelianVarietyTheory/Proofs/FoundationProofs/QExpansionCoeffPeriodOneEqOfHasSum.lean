import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory Filter Topology
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

/- English proof (translation)
Establish `h1` using `Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq1 hq0`. Set `τ : ℍ` to `⟨Function.Periodic.invQParam 1 q, h1⟩`. Establish `h2` using `Function.Periodic.cuspFunction_eq_of_nonzero 1 (f ∘ ofComplex) hq0`. Establish `h3 : cuspFunction 1 f q = f τ`. Simplify `h2` using `[cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1]`.

Establish `h4 : Function.Periodic.qParam 1 (τ : ℂ) = q` using `Function.Periodic.qParam_right_inv one_ne_zero hq0`. Rewrite using `[h3, ← h4]`. Conclude with `hs τ`.
-/
theorem hasSum_cuspFunction_of_hasSum {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ))
    {q : ℂ} (hq0 : q ≠ 0) (hq1 : ‖q‖ < 1) :
    HasSum (fun m => a m • q ^ m) (cuspFunction 1 f q) := by
  have h1 := Function.Periodic.im_invQParam_pos_of_norm_lt_one one_pos hq1 hq0
  let τ : ℍ := ⟨Function.Periodic.invQParam 1 q, h1⟩
  have h2 := Function.Periodic.cuspFunction_eq_of_nonzero 1 (f ∘ ofComplex) hq0
  have h3 : cuspFunction 1 f q = f τ := by
    simpa [cuspFunction, UpperHalfPlane.ofComplex_apply_of_im_pos h1] using h2
  have h4 : Function.Periodic.qParam 1 (τ : ℂ) = q :=
    Function.Periodic.qParam_right_inv one_ne_zero hq0
  rw [h3, ← h4]
  exact hs τ

/- English proof (translation)
Use `set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp`. Establish `hrad : 1 ≤ p.radius`. Use `ENNReal.le_of_forall_nnreal_lt fun r hr => ?_` and prove the remaining obligations. Break down `eq_or_ne r 0 with rfl | hr0` into its components or cases. Simplify using the standard rewrite rules.

Establish `hq0 : ((r : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hr0`. Establish `hq1 : ‖((r : ℝ) : ℂ)‖ < 1`. Establish `: (r : ℝ) < 1` using `by exact_mod_cast hr`. Simplify using `using this`. Establish `ht` using `(hasSum_cuspFunction_of_hasSum hs hq0 hq1).summable.tendsto_atTop_zero.norm`.

Use `p.le_radius_of_tendsto (l := 0) ?_` and prove the remaining obligations. Establish `ht' : Tendsto (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n) atTop (𝓝 0)` using `by simpa using ht`. Use `ht' using 2 with n` and compare the differences between its conclusion and the goal. Simplify using `[hp, FormalMultilinearSeries.ofScalars_norm]`. Establish `hpos : 0 < p.radius` using `lt_of_lt_of_le zero_lt_one hrad`.

Establish `hP` using `p.hasFPowerSeriesOnBall hpos`. Establish `hAn : AnalyticAt ℂ p.sum 0` using `hP.analyticAt`. Establish `hne : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → cuspFunction 1 f q = p.sum q`. Introduce `q hq0 hq1`. Rewrite using `[hp, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq a q, (hasSum_cuspFunction_of_hasSum hs hq0 hq1).tsum_eq]`.

Establish `hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ)` using `Metric.ball_mem_nhds 0 one_pos`. Establish `hev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction 1 f q = p.sum q` using `by filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with q hq hq0`. Conclude with `hne q hq0 (by simpa using hq)`. Establish `h0 : cuspFunction 1 f 0 = p.sum 0`. Establish `ht : Tendsto (cuspFunction 1 f) (𝓝[≠] 0) (𝓝 (p.sum 0))` using `(hAn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun q hq => hq.symm)`.

Simplify using `only [cuspFunction, Function.Periodic.cuspFunction, Function.update_self]`. Use `Tendsto.limUnder_eq ?_` and prove the remaining obligations. Use `ht.congr' ?_` and prove the remaining obligations. Use `filter_upwards [self_mem_nhdsWithin] with q hq0`. Simplify using `[cuspFunction, Function.Periodic.cuspFunction, Function.update_of_ne hq0]`.

Use `hAn.congr ?_` and prove the remaining obligations. Use `filter_upwards [hball] with q hq`. Break down `eq_or_ne q 0 with rfl | hq0` into its components or cases. Conclude with `h0.symm`. Conclude with `(hne q hq0 (by simpa using hq)).symm`.
-/
theorem analyticAt_cuspFunction_of_hasSum {f : ℍ → ℂ} {a : ℕ → ℂ}
    (hs : ∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) :
    AnalyticAt ℂ (cuspFunction 1 f) 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hrad : 1 ≤ p.radius := by
    refine ENNReal.le_of_forall_nnreal_lt fun r hr => ?_
    rcases eq_or_ne r 0 with rfl | hr0
    · simp
    have hq0 : ((r : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hr0
    have hq1 : ‖((r : ℝ) : ℂ)‖ < 1 := by
      have : (r : ℝ) < 1 := by exact_mod_cast hr
      simpa using this
    have ht := (hasSum_cuspFunction_of_hasSum hs hq0 hq1).summable.tendsto_atTop_zero.norm
    refine p.le_radius_of_tendsto (l := 0) ?_
    have ht' : Tendsto (fun n : ℕ => ‖a n‖ * (r : ℝ) ^ n) atTop (𝓝 0) := by simpa using ht
    convert ht' using 2 with n
    simp [hp, FormalMultilinearSeries.ofScalars_norm]
  have hpos : 0 < p.radius := lt_of_lt_of_le zero_lt_one hrad
  have hP := p.hasFPowerSeriesOnBall hpos
  have hAn : AnalyticAt ℂ p.sum 0 := hP.analyticAt
  have hne : ∀ q : ℂ, q ≠ 0 → ‖q‖ < 1 → cuspFunction 1 f q = p.sum q := by
    intro q hq0 hq1
    rw [hp, ← FormalMultilinearSeries.ofScalarsSum, FormalMultilinearSeries.ofScalars_sum_eq a q,
      (hasSum_cuspFunction_of_hasSum hs hq0 hq1).tsum_eq]
  have hball : Metric.ball (0 : ℂ) 1 ∈ 𝓝 (0 : ℂ) := Metric.ball_mem_nhds 0 one_pos
  have hev : ∀ᶠ q in 𝓝[≠] (0 : ℂ), cuspFunction 1 f q = p.sum q := by
    filter_upwards [nhdsWithin_le_nhds hball, self_mem_nhdsWithin] with q hq hq0
    exact hne q hq0 (by simpa using hq)
  have h0 : cuspFunction 1 f 0 = p.sum 0 := by
    have ht : Tendsto (cuspFunction 1 f) (𝓝[≠] 0) (𝓝 (p.sum 0)) :=
      (hAn.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' (hev.mono fun q hq => hq.symm)
    simp only [cuspFunction, Function.Periodic.cuspFunction, Function.update_self]
    refine Tendsto.limUnder_eq ?_
    refine ht.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with q hq0
    simp [cuspFunction, Function.Periodic.cuspFunction, Function.update_of_ne hq0]
  refine hAn.congr ?_
  filter_upwards [hball] with q hq
  rcases eq_or_ne q 0 with rfl | hq0
  · exact h0.symm
  · exact (hne q hq0 (by simpa using hq)).symm

/- English proof (translation)
Introduce `f a hs n`. Establish `han` using `analyticAt_cuspFunction_of_hasSum hs`. Establish `h1` using `(hasFPowerSeriesOnBall_cuspFunction one_pos han hs).hasFPowerSeriesAt`. Establish `h2 : HasFPowerSeriesAt (cuspFunction 1 f) (FormalMultilinearSeries.ofScalars ℂ fun m => coef f m) 0`. Simplify `han.hasFPowerSeriesAt` using `[coef, qExpansion_coeff, div_eq_mul_inv, mul_comm]`.

Simplify using `using congr_arg (FormalMultilinearSeries.coeff · n) (h2.eq_formalMultilinearSeries h1)`.
-/
theorem coef_of_hasSum : ∀ (f : ℍ → ℂ) (a : ℕ → ℂ),
    (∀ τ : ℍ, HasSum (fun m => a m • Function.Periodic.qParam 1 τ ^ m) (f τ)) →
      ∀ n, GlobalTheory.Hk.coef f n = a n := by
  intro f a hs n
  have han := analyticAt_cuspFunction_of_hasSum hs
  have h1 := (hasFPowerSeriesOnBall_cuspFunction one_pos han hs).hasFPowerSeriesAt
  have h2 : HasFPowerSeriesAt (cuspFunction 1 f)
      (FormalMultilinearSeries.ofScalars ℂ fun m => coef f m) 0 := by
    simpa [coef, qExpansion_coeff, div_eq_mul_inv, mul_comm] using han.hasFPowerSeriesAt
  simpa using congr_arg (FormalMultilinearSeries.coeff · n) (h2.eq_formalMultilinearSeries h1)

end GlobalTheory.Hk
