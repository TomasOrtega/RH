import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VolumeOfBallBound
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepReal.volBall` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FVolumeOfBallBound.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.volume_of_ball_bound : VolBall := by
  first | exact @GlobalTheory.SepReal.volBall | exact GlobalTheory.SepReal.volBall | (intros; apply GlobalTheory.SepReal.volBall <;> assumption)
