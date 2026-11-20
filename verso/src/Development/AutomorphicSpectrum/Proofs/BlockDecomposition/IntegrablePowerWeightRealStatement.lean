import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrablePowerWeightReal
import Mathlib
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntegrablePowerWeightReal.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.integrable_power_weight_real : ∀ (r N : ℝ), -1 < r → r + 1 < N → MeasureTheory.Integrable (fun x : ℝ => |x| ^ r * (1 + |x|) ^ (-N)) := by
  first | exact @GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow | exact GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow | (intros; apply GlobalTheory.CompanionTheory.RealTateConv.integrable_abs_rpow_mul_one_add_abs_rpow <;> assumption)
