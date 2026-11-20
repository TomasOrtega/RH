import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall.Fin3

/- English proof (translation)
Rewrite using `[Complex.conj_mul', show (1 : ℂ) + (‖z‖ : ℂ) ^ 2 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring, Complex.norm_of_nonneg (by positivity)]`.
-/
theorem norm_one_add_conj_mul (z : ℂ) : ‖1 + (starRingEnd ℂ) z * z‖ = 1 + ‖z‖ ^ 2 := by
  rw [Complex.conj_mul', show (1 : ℂ) + (‖z‖ : ℂ) ^ 2 = ((1 + ‖z‖ ^ 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_of_nonneg (by positivity)]

/- English proof (translation)
Simplify using `[gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]`. Rewrite using `[norm_one_add_conj_mul]`.
-/
theorem gB_one (w : Low 3 → ℂ) : gB 1 w = (1 + ‖w ⟨(2, 1), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

/- English proof (translation)
Simplify using `[gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]`. Rewrite using `[norm_one_add_conj_mul]`.
-/
theorem gB_two (w : Low 3 → ℂ) : gB 2 w = (1 + ‖w ⟨(1, 0), by decide⟩‖ ^ 2) ^ (-2 : ℤ) := by
  simp [gB, Fin.prod_univ_two, colGram, lminor, Matrix.det_fin_one, Matrix.mul_apply, Fin.sum_univ_two, blkW, lowMat]
  rw [norm_one_add_conj_mul]

noncomputable def dom (x : ℂ) : ℝ≥0∞ :=
  (Metric.closedBall (0 : ℂ) 1).indicator 1 x + ENNReal.ofReal ((1 + ‖x‖ ^ 2) ^ (-(4 : ℝ) / 2))

/- English proof (translation)
Unfold `dom`. Use `Measurable.add ((measurable_const).indicator Metric.isClosed_closedBall.measurableSet) ?_` and prove the remaining obligations. Conclude with `ENNReal.measurable_ofReal.comp (by fun_prop)`.
-/
theorem measurable_dom : Measurable dom := by
  unfold dom
  refine Measurable.add ((measurable_const).indicator Metric.isClosed_closedBall.measurableSet) ?_
  exact ENNReal.measurable_ofReal.comp (by fun_prop)

/- English proof (translation)
Unfold `dom`. Rewrite using `[lintegral_add_left (f := (Metric.closedBall (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞)) (measurable_one.indicator Metric.isClosed_closedBall.measurableSet)]`. Use `ENNReal.add_lt_top.2 ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]`. Conclude with `measure_closedBall_lt_top`.

Conclude with `(integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4) (by rw [Complex.finrank_real_complex]; norm_num)).lintegral_lt_top`.
-/
theorem lintegral_dom_lt_top : ∫⁻ x, dom x < ⊤ := by
  unfold dom
  rw [lintegral_add_left (f := (Metric.closedBall (0 : ℂ) 1).indicator (1 : ℂ → ℝ≥0∞))
    (measurable_one.indicator Metric.isClosed_closedBall.measurableSet)]
  refine ENNReal.add_lt_top.2 ⟨?_, ?_⟩
  · rw [lintegral_indicator_one Metric.isClosed_closedBall.measurableSet]
    exact measure_closedBall_lt_top
  · exact (integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 4)
      (by rw [Complex.finrank_real_complex]; norm_num)).lintegral_lt_top

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]`. Combine the equalities or inequalities in the displayed calculation. Use `mul_le_mul' ?_ ?_` and prove the remaining obligations. Unfold `dom`. Use `le_trans (le_of_eq ?_) le_add_self` and prove the remaining obligations.

Use `congr 1`. Rewrite using `[show (-(4 : ℝ) / 2) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]`. Use `Finset.one_le_prod' fun p hp => ?_` and prove the remaining obligations. Unfold `dom`. Use `le_trans (le_of_eq ?_) le_self_add` and prove the remaining obligations.

Rewrite using `[Set.indicator_of_mem (by simpa using hw p (Finset.ne_of_mem_erase hp))]`. Both sides reduce to the same expression.
-/
theorem le_prod_dom (w : Low 3 → ℂ) (e : Low 3) (hw : ∀ p, p ≠ e → ‖w p‖ ≤ 1) :
    ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) ≤ ∏ p, dom (w p) := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ e)]
  calc ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) = ENNReal.ofReal ((1 + ‖w e‖ ^ 2) ^ (-2 : ℤ)) * 1 :=
        (mul_one _).symm
    _ ≤ dom (w e) * ∏ p ∈ Finset.univ.erase e, dom (w p) := by
      refine mul_le_mul' ?_ ?_
      · unfold dom
        refine le_trans (le_of_eq ?_) le_add_self
        congr 1
        rw [show (-(4 : ℝ) / 2) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
      · refine Finset.one_le_prod' fun p hp => ?_
        unfold dom
        refine le_trans (le_of_eq ?_) le_self_add
        rw [Set.indicator_of_mem (by simpa using hw p (Finset.ne_of_mem_erase hp))]
        rfl

/- English proof (translation)
Unfold `hB`. Distinguish the cases in `hS : w ∈ {w : Low 3 → ℂ | ∀ p : Low 3, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}`. Rewrite using `[Set.indicator_of_mem hS]`. Break down `hp with rfl | rfl` into its components or cases. Rewrite using `[gB_one]`.

Use `le_prod_dom w _ fun p hpe => hS p ?_ ?_` and prove the remaining obligations. Use `revert hpe`. Use `revert p`. Evaluate the decidable proposition. Use `revert hpe`.

Use `revert p`. Evaluate the decidable proposition. Rewrite using `[gB_two]`. Use `le_prod_dom w _ fun p hpe => hS p ?_ ?_` and prove the remaining obligations. Use `revert hpe`.

Use `revert p`. Evaluate the decidable proposition. Use `revert hpe`. Use `revert p`. Evaluate the decidable proposition.

Rewrite using `[Set.indicator_of_notMem hS]`. Conclude with `bot_le`.
-/
theorem hB_le (p0 : ℕ) (hp : p0 = 1 ∨ p0 = 2) (w : Low 3 → ℂ) : hB p0 w ≤ ∏ p, dom (w p) := by
  unfold hB
  by_cases hS : w ∈ {w : Low 3 → ℂ | ∀ p : Low 3, (p.1.2 : ℕ) < p0 → p0 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
  · rw [Set.indicator_of_mem hS]
    rcases hp with rfl | rfl
    · rw [gB_one]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
    · rw [gB_two]
      refine le_prod_dom w _ fun p hpe => hS p ?_ ?_
      · revert hpe; revert p; decide
      · revert hpe; revert p; decide
  · rw [Set.indicator_of_notMem hS]
    exact bot_le

/- English proof (translation)
Introduce `p0 hp`. Use `lt_of_le_of_lt (lintegral_mono fun w => hB_le p0 hp w) ?_` and prove the remaining obligations. Establish `h` using `GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (E := fun _ : Low 3 => ℂ) (μ := fun _ => (volume : Measure ℂ)) (f := fun _ => dom) (fun _ => measurable_dom.aemeasurable)`. Rewrite using `[volume_pi, h]`. Conclude with `ENNReal.prod_lt_top fun _ _ => lintegral_dom_lt_top`.
-/
theorem lintegral_hB_lt_top : ∀ p0 : ℕ, (p0 = 1 ∨ p0 = 2) → ∫⁻ w : Low 3 → ℂ, hB p0 w < ⊤ := by
  intro p0 hp
  refine lt_of_le_of_lt (lintegral_mono fun w => hB_le p0 hp w) ?_
  have h := GlobalTheory.RestrMeas.lintegral_fintype_prod_eq_prod (E := fun _ : Low 3 => ℂ)
    (μ := fun _ => (volume : Measure ℂ)) (f := fun _ => dom) (fun _ => measurable_dom.aemeasurable)
  rw [volume_pi, h]
  exact ENNReal.prod_lt_top fun _ _ => lintegral_dom_lt_top

end GlobalTheory.IntBall.Fin3
