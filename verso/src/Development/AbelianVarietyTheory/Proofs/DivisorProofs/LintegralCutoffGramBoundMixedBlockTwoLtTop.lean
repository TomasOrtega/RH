import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NmatEqLowMat
open ReciprocityTheory.ChartRestriction.G.FD MeasureTheory GlobalTheory.IntBall
open scoped ENNReal Matrix

namespace GlobalTheory.IntBall

/- English proof (translation)
Establish `hg : ∀ w : Low 2 → ℂ, gB 1 w = 1`. Introduce `w`. Simplify using `[gB, colGram, lminor]`. Establish `hset : {w : Low 2 → ℂ | ∀ p : Low 2, (p.1.2 : ℕ) < 1 → 1 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1} = Metric.closedBall (0 : Low 2 → ℂ) 1`. Use extensionality with `w`.

Simplify using `only [Set.mem_setOf_eq, mem_closedBall_zero_iff]`. Rewrite using `[pi_norm_le_iff_of_nonneg zero_le_one]`. Prove the components needed by the constructor for the conclusion. Introduce `h p`. Establish `hp` using `p.2`.

Establish `h1 : (p.1.2 : ℕ) < p.1.1` using `hp`. Establish `h2 : (p.1.1 : ℕ) < 2` using `p.1.1.isLt`. Conclude with `h p (by omega) (by omega)`. Introduce `h p _ _`. Conclude with `h p`.

Establish `hfun : hB 1 = Set.indicator (Metric.closedBall (0 : Low 2 → ℂ) 1) (fun _ => (1 : ℝ≥0∞))`. Use function extensionality and compare the values at `w`. Simplify using `only [hB, hset, hg, ENNReal.ofReal_one]`. Rewrite using `[hfun, lintegral_indicator Metric.isClosed_closedBall.measurableSet]`. Simplify using `only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]`.

Conclude with `measure_closedBall_lt_top`.
-/
theorem lintegral_hB_one_two_lt_top : ∫⁻ w : Low 2 → ℂ, hB 1 w < ⊤ := by
  have hg : ∀ w : Low 2 → ℂ, gB 1 w = 1 := by
    intro w
    simp [gB, colGram, lminor]
  have hset : {w : Low 2 → ℂ | ∀ p : Low 2, (p.1.2 : ℕ) < 1 → 1 ≤ (p.1.1 : ℕ) → ‖w p‖ ≤ 1}
      = Metric.closedBall (0 : Low 2 → ℂ) 1 := by
    ext w
    simp only [Set.mem_setOf_eq, mem_closedBall_zero_iff]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    constructor
    · intro h p
      have hp := p.2
      have h1 : (p.1.2 : ℕ) < p.1.1 := hp
      have h2 : (p.1.1 : ℕ) < 2 := p.1.1.isLt
      exact h p (by omega) (by omega)
    · intro h p _ _
      exact h p
  have hfun : hB 1 = Set.indicator (Metric.closedBall (0 : Low 2 → ℂ) 1) (fun _ => (1 : ℝ≥0∞)) := by
    funext w
    simp only [hB, hset, hg, ENNReal.ofReal_one]
  rw [hfun, lintegral_indicator Metric.isClosed_closedBall.measurableSet]
  simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter, one_mul]
  exact measure_closedBall_lt_top

end GlobalTheory.IntBall
