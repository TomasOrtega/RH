import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJ
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.RealPlaceAnalysis.FinalF
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BallVol.ballVol` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHaarBallGrowthUnitaryJ.lean&line=145#L145)
-/
theorem _root_.GlobalTheory.T.haar_ball_growth_unitaryJ : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, (∀ R : ℝ, 1 ≤ R → muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (4 * n * rkR ε))) ∧ ∀ r : ℝ, 0 ≤ r → muG ε {g | dOp (uMat g) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
  first | exact @GlobalTheory.BallVol.ballVol | exact GlobalTheory.BallVol.ballVol | (intros; apply GlobalTheory.BallVol.ballVol <;> assumption)
