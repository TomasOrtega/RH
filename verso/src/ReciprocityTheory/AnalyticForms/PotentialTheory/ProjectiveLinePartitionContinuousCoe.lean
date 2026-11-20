import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.IntegralIoiFsDensRadial

namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint Filter Topology Set

noncomputable section

def p1i0 : Fin p1.n := ⟨0, by show 0 < 2; norm_num⟩

def p1i1 : Fin p1.n := ⟨1, by show 1 < 2; norm_num⟩

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. It suffices to derive a contradiction. Separate the alternatives or extract the components of the hypothesis. Establish an intermediate fact. A detailed English derivation is pending.
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
Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem projectiveLine_locDens_first_chart (y : Fin 1 → ℂ) : locDens p1 (fun _ => fsPot) p1i0 y = fsDens (y 0) := by
  apply maDens_fs
  refine Filter.Eventually.of_forall fun y' => ?_
  show fsPot.φ ((y 0 : ℂ) : OnePoint ℂ) ((y' 0 : ℂ) : OnePoint ℂ) = _
  simp only [fsPot, if_neg (coe_ne_infty _)]
  rfl

/- English proof (translation)
Consider separately whether the proposition holds or fails. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

A detailed English derivation is pending.
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
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem projectiveLine_partition_continuous_coe (P : ChartPartition p1) (j : Fin p1.n) :
    Continuous fun u : ℂ => P.χ j (u : OnePoint ℂ) := by
  have h := (P.smooth j p1i0).continuousOn
  rw [show (p1.chart p1i0).target = univ from rfl, preimage_univ, inter_univ,
    continuousOn_univ] at h
  exact h.comp (continuous_pi fun _ => continuous_id)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem projectiveLine_partition_integrable (P : ChartPartition p1) (j : Fin p1.n) :
    Integrable fun u : ℂ => P.χ j (u : OnePoint ℂ) * fsDens u := by
  refine integrable_fsDens.bdd_mul (c := 1) (projectiveLine_partition_continuous_coe P j).aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (P.nonneg j _), ← P.sum_eq_one (u : OnePoint ℂ)]
  exact Finset.single_le_sum (fun i _ => P.nonneg i _) (Finset.mem_univ j)

/- English proof (translation)
Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion repeatedly using the stated equalities. A detailed English derivation is pending.
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
Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem projectiveLine_fubiniStudy_mass_one : mInt p1 (fun _ => fsPot) (fun _ => 1) = 1 := by
  rw [mInt, dif_pos projLine_partition]
  exact projectiveLine_integralWith_eq_one _

end

end ReciprocityTheory.AnForm.M
