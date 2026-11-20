import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegralIoiFsDensRadial

namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint Filter Topology Set

noncomputable section

def p1i0 : Fin p1.n := ⟨0, by show 0 < 2; norm_num⟩

def p1i1 : Fin p1.n := ⟨1, by show 1 < 2; norm_num⟩

/- English proof (translation)
Use `Fintype.sum_eq_add p1i0 p1i1 (fun h => by simpa [p1i0, p1i1] using congrArg Fin.val h) (fun j hj => ?_)` and prove the remaining obligations. It suffices to derive a contradiction. Break down `j with ⟨k, hk⟩` into its components or cases. Establish `hk2 : k < 2` using `hk`. Use `interval_cases k`.

Conclude with `hj.1 rfl`. Conclude with `hj.2 rfl`.
-/
theorem projectiveLine_sum_charts (f : Fin p1.n → ℝ) : ∑ j, f j = f p1i0 + f p1i1 := by
  refine Fintype.sum_eq_add p1i0 p1i1 (fun h => by simpa [p1i0, p1i1] using congrArg Fin.val h)
    (fun j hj => ?_)
  exfalso
  rcases j with ⟨k, hk⟩
  have hk2 : k < 2 := hk
  interval_cases k
  · exact hj.1 rfl
  · exact hj.2 rfl

open scoped Classical in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem projectiveLine_second_chart_symm (y : Fin 1 → ℂ) :
    (p1.chart p1i1).symm y = if y 0 = 0 then ∞ else (((y 0)⁻¹ : ℂ) : OnePoint ℂ) := rfl

/- English proof (translation)
Apply `maDens_fs` to reduce the goal to its premises. Use `Filter.Eventually.of_forall fun y' => ?_` and prove the remaining obligations. Use `show fsPot.φ ((y 0 : ℂ) : OnePoint ℂ) ((y' 0 : ℂ) : OnePoint ℂ) = _`. Simplify using `only [fsPot, if_neg (coe_ne_infty _)]`. Both sides reduce to the same expression.
-/
theorem projectiveLine_locDens_first_chart (y : Fin 1 → ℂ) : locDens p1 (fun _ => fsPot) p1i0 y = fsDens (y 0) := by
  apply maDens_fs
  refine Filter.Eventually.of_forall fun y' => ?_
  show fsPot.φ ((y 0 : ℂ) : OnePoint ℂ) ((y' 0 : ℂ) : OnePoint ℂ) = _
  simp only [fsPot, if_neg (coe_ne_infty _)]
  rfl

/- English proof (translation)
Distinguish the cases in `hy : y 0 = 0`. Apply `maDens_fs` to reduce the goal to its premises. Use `Filter.Eventually.of_forall fun y' => ?_` and prove the remaining obligations. Use `show fsPot.φ ((p1.chart p1i1).symm y) ((p1.chart p1i1).symm y') = _`. Rewrite using `[projectiveLine_second_chart_symm, projectiveLine_second_chart_symm, if_pos hy]`.

Simplify using `only [fsPot]`. Distinguish the cases in `hy' : y' 0 = 0`. Rewrite using `[if_pos hy', hy']`. Simplify using `[crd1]`. Rewrite using `[if_neg hy']`.

Simplify using `[crd1]`. Apply `maDens_fs_inv _ _ hy` to reduce the goal to its premises. Establish `hne : ∀ᶠ y' in 𝓝 y, y' 0 ≠ 0` using `(continuous_apply 0).continuousAt.eventually_ne hy`. Use `filter_upwards [hne] with y' hy'`. Use `show fsPot.φ ((p1.chart p1i1).symm y) ((p1.chart p1i1).symm y') = _`.

Rewrite using `[projectiveLine_second_chart_symm, projectiveLine_second_chart_symm, if_neg hy, if_neg hy']`. Simplify using `only [fsPot, if_neg (coe_ne_infty _)]`. Both sides reduce to the same expression.
-/
theorem projectiveLine_locDens_second_chart (y : Fin 1 → ℂ) : locDens p1 (fun _ => fsPot) p1i1 y = fsDens (y 0) := by
  by_cases hy : y 0 = 0
  · apply maDens_fs
    refine Filter.Eventually.of_forall fun y' => ?_
    show fsPot.φ ((p1.chart p1i1).symm y) ((p1.chart p1i1).symm y') = _
    rw [projectiveLine_second_chart_symm, projectiveLine_second_chart_symm, if_pos hy]
    simp only [fsPot]
    by_cases hy' : y' 0 = 0
    · rw [if_pos hy', hy']
      simp [crd1]
    · rw [if_neg hy']
      simp [crd1]
  · apply maDens_fs_inv _ _ hy
    have hne : ∀ᶠ y' in 𝓝 y, y' 0 ≠ 0 :=
      (continuous_apply 0).continuousAt.eventually_ne hy
    filter_upwards [hne] with y' hy'
    show fsPot.φ ((p1.chart p1i1).symm y) ((p1.chart p1i1).symm y') = _
    rw [projectiveLine_second_chart_symm, projectiveLine_second_chart_symm, if_neg hy, if_neg hy']
    simp only [fsPot, if_neg (coe_ne_infty _)]
    rfl

/- English proof (translation)
Establish `h` using `(P.smooth j p1i0).continuousOn`. Rewrite `h` using `[show (p1.chart p1i0).target = univ from rfl, preimage_univ, inter_univ, continuousOn_univ]`. Conclude with `h.comp (continuous_pi fun _ => continuous_id)`.
-/
theorem projectiveLine_partition_continuous_coe (P : ChartPartition p1) (j : Fin p1.n) :
    Continuous fun u : ℂ => P.χ j (u : OnePoint ℂ) := by
  have h := (P.smooth j p1i0).continuousOn
  rw [show (p1.chart p1i0).target = univ from rfl, preimage_univ, inter_univ,
    continuousOn_univ] at h
  exact h.comp (continuous_pi fun _ => continuous_id)

/- English proof (translation)
Use `integrable_fsDens.bdd_mul (c := 1) (projectiveLine_partition_continuous_coe P j).aestronglyMeasurable (Filter.Eventually.of_forall fun u => ?_)` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _), ← P.sum_eq_one (u : OnePoint ℂ)]`. Conclude with `Finset.single_le_sum (fun i _ => P.nonneg i _) (Finset.mem_univ j)`.
-/
theorem projectiveLine_partition_integrable (P : ChartPartition p1) (j : Fin p1.n) :
    Integrable fun u : ℂ => P.χ j (u : OnePoint ℂ) * fsDens u := by
  refine integrable_fsDens.bdd_mul (c := 1) (projectiveLine_partition_continuous_coe P j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _), ← P.sum_eq_one (u : OnePoint ℂ)]
  exact Finset.single_le_sum (fun i _ => P.nonneg i _) (Finset.mem_univ j)

/- English proof (translation)
Unfold `integralWith`. Rewrite using `[projectiveLine_sum_charts]`. Establish `e0 : ∫ y in (p1.chart p1i0).target, P.χ p1i0 ((p1.chart p1i0).symm y) * (fun _ => (1 : ℝ)) ((p1.chart p1i0).symm y) * locDens p1 (fun _ => fsPot) p1i0 y = ∫ u : ℂ, P.χ p1i0 (u : OnePoint ℂ) * fsDens u`. Rewrite using `[show (p1.chart p1i0).target = univ from rfl, Measure.restrict_univ]`. Repeatedly rewrite using `[projectiveLine_locDens_first_chart, mul_one]`.

Conclude with `(volume_preserving_funUnique (Fin 1) ℂ).integral_comp' (fun u => P.χ p1i0 (u : OnePoint ℂ) * fsDens u)`. Establish `e1 : ∫ y in (p1.chart p1i1).target, P.χ p1i1 ((p1.chart p1i1).symm y) * (fun _ => (1 : ℝ)) ((p1.chart p1i1).symm y) * locDens p1 (fun _ => fsPot) p1i1 y = ∫ u : ℂ, P.χ p1i1 (u : OnePoint ℂ) * fsDens u`. Rewrite using `[show (p1.chart p1i1).target = univ from rfl, Measure.restrict_univ]`. Repeatedly rewrite using `[projectiveLine_locDens_second_chart, mul_one]`. Rewrite using `[← integral_fsDens_inv (fun v => P.χ p1i1 (v : OnePoint ℂ))]`.

Use `Eq.trans ((volume_preserving_funUnique (Fin 1) ℂ).integral_comp' (fun u => P.χ p1i1 ((p1.chart p1i1).symm (fun _ => u)) * fsDens u)) ?_` and prove the remaining obligations. Use `integral_congr_ae ?_` and prove the remaining obligations. Use `filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with u hu`. Establish `hu0 : u ≠ 0` using `hu`. Use `show P.χ p1i1 ((p1.chart p1i1).symm (fun _ => u)) * fsDens u = P.χ p1i1 (u⁻¹ : ℂ) * fsDens u`.

Rewrite using `[projectiveLine_second_chart_symm, if_neg hu0]`. Rewrite using `[e0, e1, ← integral_add (projectiveLine_partition_integrable P p1i0) (projectiveLine_partition_integrable P p1i1)]`. Repeatedly rewrite using `[← add_mul]`. Establish `hs : ∀ u : ℂ, P.χ p1i0 (u : OnePoint ℂ) + P.χ p1i1 (u : OnePoint ℂ) = 1` using `fun u => by`. Rewrite using `[← projectiveLine_sum_charts (fun j => P.χ j (u : OnePoint ℂ)), P.sum_eq_one]`.

Repeatedly rewrite using `[hs, one_mul]`. Conclude with `integral_fsDens`.
-/
theorem projectiveLine_integralWith_eq_one (P : ChartPartition p1) :
    integralWith p1 P (fun _ => fsPot) (fun _ => 1) = 1 := by
  unfold integralWith
  rw [projectiveLine_sum_charts]
  have e0 : ∫ y in (p1.chart p1i0).target,
      P.χ p1i0 ((p1.chart p1i0).symm y) * (fun _ => (1 : ℝ)) ((p1.chart p1i0).symm y) *
        locDens p1 (fun _ => fsPot) p1i0 y = ∫ u : ℂ, P.χ p1i0 (u : OnePoint ℂ) * fsDens u := by
    rw [show (p1.chart p1i0).target = univ from rfl, Measure.restrict_univ]
    simp_rw [projectiveLine_locDens_first_chart, mul_one]
    exact (volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
      (fun u => P.χ p1i0 (u : OnePoint ℂ) * fsDens u)
  have e1 : ∫ y in (p1.chart p1i1).target,
      P.χ p1i1 ((p1.chart p1i1).symm y) * (fun _ => (1 : ℝ)) ((p1.chart p1i1).symm y) *
        locDens p1 (fun _ => fsPot) p1i1 y = ∫ u : ℂ, P.χ p1i1 (u : OnePoint ℂ) * fsDens u := by
    rw [show (p1.chart p1i1).target = univ from rfl, Measure.restrict_univ]
    simp_rw [projectiveLine_locDens_second_chart, mul_one]
    rw [← integral_fsDens_inv (fun v => P.χ p1i1 (v : OnePoint ℂ))]
    refine Eq.trans ((volume_preserving_funUnique (Fin 1) ℂ).integral_comp'
      (fun u => P.χ p1i1 ((p1.chart p1i1).symm (fun _ => u)) * fsDens u)) ?_
    refine integral_congr_ae ?_
    filter_upwards [compl_mem_ae_iff.mpr (measure_singleton (0 : ℂ))] with u hu
    have hu0 : u ≠ 0 := hu
    show P.χ p1i1 ((p1.chart p1i1).symm (fun _ => u)) * fsDens u = P.χ p1i1 (u⁻¹ : ℂ) * fsDens u
    rw [projectiveLine_second_chart_symm, if_neg hu0]
  rw [e0, e1, ← integral_add (projectiveLine_partition_integrable P p1i0) (projectiveLine_partition_integrable P p1i1)]
  simp_rw [← add_mul]
  have hs : ∀ u : ℂ, P.χ p1i0 (u : OnePoint ℂ) + P.χ p1i1 (u : OnePoint ℂ) = 1 := fun u => by
    rw [← projectiveLine_sum_charts (fun j => P.χ j (u : OnePoint ℂ)), P.sum_eq_one]
  simp_rw [hs, one_mul]
  exact integral_fsDens

/- English proof (translation)
Rewrite using `[mInt, dif_pos projLine_partition]`. Conclude with `projectiveLine_integralWith_eq_one _`.
-/
theorem projectiveLine_fubiniStudy_mass_one : mInt p1 (fun _ => fsPot) (fun _ => 1) = 1 := by
  rw [mInt, dif_pos projLine_partition]
  exact projectiveLine_integralWith_eq_one _

end

end ReciprocityTheory.AnForm.M
