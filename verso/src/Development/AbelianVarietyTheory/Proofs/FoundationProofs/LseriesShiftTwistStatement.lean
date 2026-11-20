import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LseriesShiftTwist
import Mathlib
open Complex Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FLseriesShiftTwist.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.lSeries_twist_natPow_eq_shift : ∀ (e : ℕ) (ψ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → LSeries (fun n : ℕ => ψ n * (n : ℂ) ^ (e - 1) * g n) (((2 * (e : ℝ) + s : ℝ)) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) := by
  first | exact @GlobalTheory.lseries_shift_twist | exact GlobalTheory.lseries_shift_twist | (intros; apply GlobalTheory.lseries_shift_twist <;> assumption)
