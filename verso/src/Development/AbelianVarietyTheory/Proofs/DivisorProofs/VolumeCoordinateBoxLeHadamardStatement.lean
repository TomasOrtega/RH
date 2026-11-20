import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VolumeCoordinateBoxLeHadamard
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ExistsOrthonormalOfLinearIndependent
open MeasureTheory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoordBox.volume_coordBox_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FVolumeCoordinateBoxLeHadamard.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.volume_coordinateBox_le_hadamard : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (K : Type) [Fintype K] (w : K → V) (t : ℝ), 0 ≤ t → Fintype.card K = Module.finrank ℝ V → MeasureTheory.volume {y : V | ∃ c : K → ℝ, (∀ k, |c k| ≤ t) ∧ y = ∑ k, c k • w k} ≤ ENNReal.ofReal ((2 * t) ^ Fintype.card K * ∏ k, ‖w k‖) := by
  first | exact @GlobalTheory.CoordBox.volume_coordBox_le | exact GlobalTheory.CoordBox.volume_coordBox_le | (intros; apply GlobalTheory.CoordBox.volume_coordBox_le <;> assumption)
