import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FirstChernLeviEqConstant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import ReciprocityTheory.AnalyticForms.PotentialTheory.LocDens
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
open Filter Topology Set Metric MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Mean4O
open scoped ContDiff

namespace GlobalTheory.Mean4O

/- English proof (translation)
Take `⟨hZ, hnull, hpot, hpos, -, hr, -, hint, -⟩` from `h`. Establish `hD` using `locDensPos A (fun _ => Om) (fun _ => hpot) (fun _ => hpos) j`. Establish `hDc` using `locDensCont A (fun _ => Om) (fun _ => hpot) j`. Rewrite using `[locallyIntegrableOn_iff (A.chart j).open_target.isLocallyClosed]`. Introduce `K hK hKc`.

Establish `hinv : ContinuousOn (fun y => |C| * (locDens A (fun _ => Om) j y)⁻¹) K` using `continuousOn_const.mul ((hDc.mono hK).inv₀ fun y hy => (hD y (hK hy)).ne')`. Establish `h1` using `(hint j K hK hKc).mul_continuousOn hinv hKc`. Establish `hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ)` using `(A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl`. Establish `hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∉ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Z` using `measure_eq_zero_iff_ae_notMem.1 (hnull j)`. Establish `hKV : K =ᵐ[volume] (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) : Set _)` using `by filter_upwards [hae] with y hy`.

Use `propext ⟨fun hyK => ⟨hyK, hK hyK, fun hz => hy ⟨hK hyK, hz⟩⟩, fun hyK => hyK.1⟩` and prove the remaining obligations. Use `Integrable.mono' h1 ?_ ?_` and prove the remaining obligations. Rewrite using `[Measure.restrict_congr_set hKV]`. Conclude with `((hu j).continuousOn.mono inter_subset_right).aestronglyMeasurable (hKc.measurableSet.inter hVo.measurableSet)`. Rewrite using `[ae_restrict_iff' hKc.measurableSet] filter_upwards [hae] with y hy hyK`.

Establish `hz : (A.chart j).symm y ∉ Z` using `fun hz => hy ⟨hK hyK, hz⟩`. Establish `hr1` using `hr _ hz`. Establish `hr0 : 1 ≤ r ((A.chart j).symm y)` using `le_trans (Real.one_le_exp zero_le_one) hr1`. Establish `hc : cut Z univ r ((A.chart j).symm y) = r ((A.chart j).symm y)` using `indicator_of_mem (show _ ∈ univ ∩ Zᶜ from ⟨mem_univ _, hz⟩) _`. Establish `hDy` using `(hD y (hK hyK)).ne'`.

Establish `he : cut Z univ r ((A.chart j).symm y) * locDens A (fun _ => Om) j y * (|C| * (locDens A (fun _ => Om) j y)⁻¹) = |C| * r ((A.chart j).symm y)`. Rewrite using `[hc]`. Clear the denominators using the available nonvanishing facts. Rewrite using `[he, Function.comp_apply, Real.norm_eq_abs]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem locallyIntegrableOn_of_log_bound (e : ℕ) (X : Type) [TopologicalSpace X] (A : FinHolAtlas e X) (Z : Set X)
    (r : X → ℝ) (Om : LocPot X) (h : IsBd A Z r Om) (u : X → ℝ) (C : ℝ) (hu : A.SmoothOn Zᶜ u)
    (hb : ∀ x, x ∉ Z → |u x| ≤ C * Real.log (r x)) (j : Fin A.n) :
    MeasureTheory.LocallyIntegrableOn (u ∘ (A.chart j).symm) (A.chart j).target MeasureTheory.volume := by
  obtain ⟨hZ, hnull, hpot, hpos, -, hr, -, hint, -⟩ := h
  have hD := locDensPos A (fun _ => Om) (fun _ => hpot) (fun _ => hpos) j
  have hDc := locDensCont A (fun _ => Om) (fun _ => hpot) j
  rw [locallyIntegrableOn_iff (A.chart j).open_target.isLocallyClosed]
  intro K hK hKc
  have hinv : ContinuousOn (fun y => |C| * (locDens A (fun _ => Om) j y)⁻¹) K :=
    continuousOn_const.mul ((hDc.mono hK).inv₀ fun y hy => (hD y (hK hy)).ne')
  have h1 := (hint j K hK hKc).mul_continuousOn hinv hKc
  have hVo : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) :=
    (A.chart j).isOpen_inter_preimage_symm hZ.isOpen_compl
  have hae : ∀ᵐ y ∂(volume : Measure (Fin e → ℂ)), y ∉ (A.chart j).target ∩ (A.chart j).symm ⁻¹' Z :=
    measure_eq_zero_iff_ae_notMem.1 (hnull j)
  have hKV : K =ᵐ[volume] (K ∩ ((A.chart j).target ∩ (A.chart j).symm ⁻¹' Zᶜ) : Set _) := by
    filter_upwards [hae] with y hy
    refine propext ⟨fun hyK => ⟨hyK, hK hyK, fun hz => hy ⟨hK hyK, hz⟩⟩, fun hyK => hyK.1⟩
  refine Integrable.mono' h1 ?_ ?_
  · rw [Measure.restrict_congr_set hKV]
    exact ((hu j).continuousOn.mono inter_subset_right).aestronglyMeasurable
      (hKc.measurableSet.inter hVo.measurableSet)
  · rw [ae_restrict_iff' hKc.measurableSet]
    filter_upwards [hae] with y hy hyK
    have hz : (A.chart j).symm y ∉ Z := fun hz => hy ⟨hK hyK, hz⟩
    have hr1 := hr _ hz
    have hr0 : 1 ≤ r ((A.chart j).symm y) := le_trans (Real.one_le_exp zero_le_one) hr1
    have hc : cut Z univ r ((A.chart j).symm y) = r ((A.chart j).symm y) :=
      indicator_of_mem (show _ ∈ univ ∩ Zᶜ from ⟨mem_univ _, hz⟩) _
    have hDy := (hD y (hK hyK)).ne'
    have he : cut Z univ r ((A.chart j).symm y) * locDens A (fun _ => Om) j y *
        (|C| * (locDens A (fun _ => Om) j y)⁻¹) = |C| * r ((A.chart j).symm y) := by
      rw [hc]; field_simp
    rw [he, Function.comp_apply, Real.norm_eq_abs]
    calc |u ((A.chart j).symm y)| ≤ C * Real.log (r ((A.chart j).symm y)) := hb _ hz
      _ ≤ |C| * Real.log (r ((A.chart j).symm y)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) (Real.log_nonneg hr0)
      _ ≤ |C| * r ((A.chart j).symm y) :=
        mul_le_mul_of_nonneg_left (Real.log_le_self (by linarith)) (abs_nonneg C)

end GlobalTheory.Mean4O
