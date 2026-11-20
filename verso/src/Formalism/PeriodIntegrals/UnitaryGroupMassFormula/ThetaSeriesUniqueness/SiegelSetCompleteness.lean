import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ThetaSeriesUniqueness.Complete

noncomputable section

namespace PI.SSU

open Complex Filter Topology

/- English proof (translation)
Introduce `f hf hper hcoef`. Use `haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩`. Establish `hpr : Function.Periodic (fun x : ℝ => f x) 1` using `fun x => by`. Simplify using `using hper (x : ℂ)`. Establish `hcont : Continuous (fun x : ℝ => f x)` using `hf.continuous.comp Complex.continuous_ofReal`.

Set `F : C(AddCircle (1 : ℝ), ℂ)` to `⟨hpr.lift, by first`. Consider the case `exact continuous_coinduced_dom.mpr hcont`. Consider the case `exact hcont.quotient_liftOn' _`. Consider the case `exact (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hcont⟩`. Establish `hF : ∀ x : ℝ, F x = f x` using `fun x => rfl`.

Establish `hcF : ∀ n : ℤ, fourierCoeff F n = 0`. Introduce `n`. Rewrite using `[fourierCoeff_eq_intervalIntegral _ n 0, zero_add]`. Establish `h1 : ∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) • F x = coef f n`. Unfold `coef`.

Use `intervalIntegral.integral_congr fun x _ => ?_` and prove the remaining obligations. Simplify using `only [fourier_coe_apply, hF, smul_eq_mul]`. Use `push_cast`. Put the polynomial expressions in normal form. Rewrite using `[h1, hcoef n, smul_zero]`.

Establish `hL : ContinuousMap.toLp (E` using `ℂ) 2 AddCircle.haarAddCircle ℂ F = 0 := by`. Establish `hs` using `hasSum_fourier_series_L2 (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F)`. Simplify using `only [fourierCoeff_toLp, hcF, zero_smul] at hs`. Conclude with `hs.unique hasSum_zero`. Establish `hF0 : F = 0` using `by first`.

Consider the case `exact ContinuousMap.toLp_injective AddCircle.haarAddCircle (hL.trans (map_zero _).symm)`. Consider the case `exact ContinuousMap.toLp_injective (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ) (hL.trans (map_zero _).symm)`. Establish `hreal : ∀ x : ℝ, f x = 0` using `fun x => by`. Use `DFunLike.congr_fun hF0 (x : AddCircle (1 : ℝ))` as an intermediate fact. Rewrite `this` using `[hF, ContinuousMap.zero_apply]`. Then use the resulting hypothesis.

Establish `han : AnalyticOnNhd ℂ f Set.univ` using `fun z _ => hf.analyticAt z`. Establish `hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0`. Establish `ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0)`. Rewrite using `[tendsto_nhdsWithin_iff]`. Use `⟨?_, Eventually.of_forall fun n => ?_⟩` and prove the remaining obligations.

Use `(Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat` as an intermediate fact. Simplify `this` using `[Function.comp_def]`. Simplify using `only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]`. Conclude with `(by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).ne'`. Conclude with `ht.frequently (Frequently.of_forall fun n => hreal _)`.

Use function extensionality and compare the values at `z`. Conclude with `han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0) hfreq (Set.mem_univ z)`.
-/
theorem siegel_set_completeness : Complete := by
  intro f hf hper hcoef
  haveI : Fact ((0 : ℝ) < 1) := ⟨one_pos⟩
  have hpr : Function.Periodic (fun x : ℝ => f x) 1 := fun x => by
    simpa using hper (x : ℂ)
  have hcont : Continuous (fun x : ℝ => f x) := hf.continuous.comp Complex.continuous_ofReal
  let F : C(AddCircle (1 : ℝ), ℂ) := ⟨hpr.lift, by
    first
      | exact continuous_coinduced_dom.mpr hcont
      | exact hcont.quotient_liftOn' _
      | exact (QuotientAddGroup.isQuotientMap_mk _).continuous_iff.mpr hcont⟩
  have hF : ∀ x : ℝ, F x = f x := fun x => rfl
  have hcF : ∀ n : ℤ, fourierCoeff F n = 0 := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral _ n 0, zero_add]
    have h1 : ∫ x in (0 : ℝ)..1, fourier (-n) (x : AddCircle (1 : ℝ)) • F x = coef f n := by
      unfold coef
      refine intervalIntegral.integral_congr fun x _ => ?_
      simp only [fourier_coe_apply, hF, smul_eq_mul]
      push_cast
      ring_nf
    rw [h1, hcoef n, smul_zero]
  have hL : ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F = 0 := by
    have hs := hasSum_fourier_series_L2 (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ F)
    simp only [fourierCoeff_toLp, hcF, zero_smul] at hs
    exact hs.unique hasSum_zero
  have hF0 : F = 0 := by
    first
      | exact ContinuousMap.toLp_injective AddCircle.haarAddCircle (hL.trans (map_zero _).symm)
      | exact ContinuousMap.toLp_injective (p := 2) (μ := AddCircle.haarAddCircle) (𝕜 := ℂ)
          (hL.trans (map_zero _).symm)
  have hreal : ∀ x : ℝ, f x = 0 := fun x => by
    have := DFunLike.congr_fun hF0 (x : AddCircle (1 : ℝ))
    rwa [hF, ContinuousMap.zero_apply] at this
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), f z = 0 := by
    have ht : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have := (Complex.continuous_ofReal.tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
        simpa [Function.comp_def] using this
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_eq_zero]
        exact (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).ne'
    exact ht.frequently (Frequently.of_forall fun n => hreal _)
  funext z
  exact han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ 0)
    hfreq (Set.mem_univ z)

end PI.SSU
