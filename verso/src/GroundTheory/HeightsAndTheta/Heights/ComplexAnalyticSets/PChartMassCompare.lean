import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetComass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetAreaCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFibreBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

open scoped ENNReal

noncomputable section

/- English proof (translation)
Introduce `n d J A φ R hJ hdim hA hφ`. Take `⟨C, hC⟩` from `h1 n d J A φ R hφ`. Take `⟨c, hc, hca⟩` from `h2 n d J A`. Use `set C' := max C 0 with hC'`. Establish `hC'0 : 0 ≤ C'` using `le_max_right _ _`.

Use `set B := Metric.closedBall (0 : Fin n → ℂ) R`. Use `⟨ENNReal.ofReal C' * c, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc, fun g hg => ?_⟩` and prove the remaining obligations. Use `set gB := B.indicator g with hgBdef`. Establish `hgB : Measurable gB` using `hg.indicator measurableSet_closedBall`. Establish `hpt : ∀ y, chartAbsDens J A gB φ y ≤ C' * sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y`.

Introduce `y`. Establish `hfin` using `(ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1`. Unfold `chartAbsDens sheetSum`. Rewrite using `[finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]`. Use `Finset.sum_le_sum fun x hx => ?_` and prove the remaining obligations.

Establish `hxf : x ∈ fibre J A y` using `hfin.mem_toFinset.mp hx`. Use `split_ifs with hs`. Simplify using `only`. Rewrite using `[← hxf.2]`. Distinguish the cases in `hxB : x ∈ B`.

Establish `hb` using `hC x ⟨hxf.1, hxB⟩ _ hs.choose_spec`. Rewrite using `[abs_mul]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `[gB, hxB]`. Simplify using the standard rewrite rules.

Establish `hnn : ∀ y, 0 ≤ chartAbsDens J A gB φ y` using `fun y => finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs; exacts [abs_nonneg _, le_rfl]`. Combine the equalities or inequalities in the displayed calculation. Use `lintegral_mono fun y => ?_` and prove the remaining obligations. Rewrite using `[Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn y), ← ENNReal.ofReal_mul hC'0]`. Conclude with `ENNReal.ofReal_le_ofReal ((hpt y).trans (mul_le_mul_of_nonneg_left (le_abs_self _) hC'0))`.

Use `_ = ENNReal.ofReal C' * ∫⁻ y, ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top`. Use `_ ≤ ENNReal.ofReal C' * (c * ∫⁻ z in zeroSetEuc J, ‖gB (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)])) := by gcongr; exact hca gB hgB`. Use `_ = ENNReal.ofReal C' * c * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ B}, ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by`. Establish `hT : MeasurableSet {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B}` using `measurableSet_closedBall.preimage (PiLp.continuous_ofLp 2 _).measurable`. Establish `hfun : (fun z : EuclideanSpace ℂ (Fin n) => ‖gB (WithLp.ofLp z)‖ₑ) = {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B}.indicator (fun z => ‖g (WithLp.ofLp z)‖ₑ)`.

Use extensionality with `z`. Apply the tactic sequence `by_cases hz : WithLp.ofLp z ∈ B <;> simp [gB, hz, Set.indicator]`. Rewrite using `[hfun, lintegral_indicator hT, Measure.restrict_restrict hT, Set.inter_comm, mul_assoc]`.
-/
theorem ChartMassCompare.proof (h1 : SheetComass.Statement) (h2 : SheetAreaCompare.Statement) :
    ChartMassCompare.Statement := by
  intro n d J A φ R hJ hdim hA hφ
  obtain ⟨C, hC⟩ := h1 n d J A φ R hφ
  obtain ⟨c, hc, hca⟩ := h2 n d J A
  set C' := max C 0 with hC'
  have hC'0 : 0 ≤ C' := le_max_right _ _
  set B := Metric.closedBall (0 : Fin n → ℂ) R
  refine ⟨ENNReal.ofReal C' * c, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hc, fun g hg => ?_⟩
  set gB := B.indicator g with hgBdef
  have hgB : Measurable gB := hg.indicator measurableSet_closedBall

  have hpt : ∀ y, chartAbsDens J A gB φ y ≤
      C' * sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y := by
    intro y
    have hfin := (ComplexSets.FibreBound.proof n d J A hJ hdim hA y).2.1
    unfold chartAbsDens sheetSum
    rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
      Finset.mul_sum]
    refine Finset.sum_le_sum fun x hx => ?_
    have hxf : x ∈ fibre J A y := hfin.mem_toFinset.mp hx
    split_ifs with hs
    · dsimp only
      rw [← hxf.2]
      by_cases hxB : x ∈ B
      · have hb := hC x ⟨hxf.1, hxB⟩ _ hs.choose_spec
        rw [abs_mul]
        calc |gB x| * |ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ hs.choose) (A *ᵥ x)|
            ≤ |gB x| * (C' * sheetJac hs.choose (A *ᵥ x)) :=
              mul_le_mul_of_nonneg_left (hb.trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
                (sheetJac_nonneg _ _))) (abs_nonneg _)
          _ = C' * (|gB x| * sheetJac hs.choose (A *ᵥ x)) := by ring
      · simp [gB, hxB]
    · simp
  have hnn : ∀ y, 0 ≤ chartAbsDens J A gB φ y := fun y =>
    finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs; exacts [abs_nonneg _, le_rfl]
  calc ∫⁻ y, ‖chartAbsDens J A gB φ y‖ₑ
      ≤ ∫⁻ y, ENNReal.ofReal C' * ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ := by
        refine lintegral_mono fun y => ?_
        rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn y),
          ← ENNReal.ofReal_mul hC'0]
        exact ENNReal.ofReal_le_ofReal ((hpt y).trans
          (mul_le_mul_of_nonneg_left (le_abs_self _) hC'0))
    _ = ENNReal.ofReal C' * ∫⁻ y, ‖sheetSum J A (fun x s => |gB x| * sheetJac s (A *ᵥ x)) y‖ₑ :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal C' * (c * ∫⁻ z in zeroSetEuc J, ‖gB (WithLp.ofLp z)‖ₑ
          ∂(μH[((2 * d : ℕ) : ℝ)])) := by gcongr; exact hca gB hgB
    _ = ENNReal.ofReal C' * c * ∫⁻ z in zeroSetEuc J ∩ {z | WithLp.ofLp z ∈ B},
          ‖g (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        have hT : MeasurableSet {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B} :=
          measurableSet_closedBall.preimage (PiLp.continuous_ofLp 2 _).measurable
        have hfun : (fun z : EuclideanSpace ℂ (Fin n) => ‖gB (WithLp.ofLp z)‖ₑ) =
            {z : EuclideanSpace ℂ (Fin n) | WithLp.ofLp z ∈ B}.indicator
              (fun z => ‖g (WithLp.ofLp z)‖ₑ) := by
          ext z
          by_cases hz : WithLp.ofLp z ∈ B <;> simp [gB, hz, Set.indicator]
        rw [hfun, lintegral_indicator hT, Measure.restrict_restrict hT, Set.inter_comm, mul_assoc]

end

end GroundTheory.Heights₂.Heights
