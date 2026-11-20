import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory

/- English proof (translation)
Introduce `n h`. Establish `hcont : Continuous fun v : Fin n → ℂ => h.norm v`. Simplify using `only [HermNorm.norm, Matrix.mulVec, dotProduct]`. Use `fun_prop`. Establish `hopen : IsOpen (ballH h)` using `isOpen_lt hcont continuous_const`.

Establish `hzero : (0 : Fin n → ℂ) ∈ ballH h` using `by show h.norm 0 < 1`. Simplify using `[HermNorm.norm]`. Establish `hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖` using `Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _`. Establish `hbdd : Bornology.IsBounded (ballH h)`. Use `(Metric.isBounded_closedBall (x := (0 : Fin n → ℂ)) (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun v hv => ?_` and prove the remaining obligations.

Rewrite using `[Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]`. Introduce `j`. Conclude with `norm_le_of_hermNorm_lt h hv j`. Conclude with `⟨hopen.measure_pos volume ⟨0, hzero⟩, hbdd.measure_lt_top⟩`.
-/
theorem BallVolume.proof : BallVolume.Statement := by
  intro n h
  have hcont : Continuous fun v : Fin n → ℂ => h.norm v := by
    simp only [HermNorm.norm, Matrix.mulVec, dotProduct]
    fun_prop
  have hopen : IsOpen (ballH h) := isOpen_lt hcont continuous_const
  have hzero : (0 : Fin n → ℂ) ∈ ballH h := by
    show h.norm 0 < 1
    simp [HermNorm.norm]
  have hR : 0 ≤ ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hbdd : Bornology.IsBounded (ballH h) := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin n → ℂ))
      (r := ∑ j', ∑ l, ‖h.mat⁻¹ j' l‖)).subset fun v hv => ?_
    rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
    intro j
    exact norm_le_of_hermNorm_lt h hv j
  exact ⟨hopen.measure_pos volume ⟨0, hzero⟩, hbdd.measure_lt_top⟩

end GroundTheory.Heights₂.Heights
