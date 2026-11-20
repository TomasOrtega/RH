import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeNormPowerIntegrableOfBallVolume
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FNegativeNormPowerIntegrableOfBallVolume.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.negativeNormPowerIntegrable_of_ballVolume : VolBall → PowInt := by
  first | exact @GlobalTheory.SepReal.powInt_of_volBall | exact GlobalTheory.SepReal.powInt_of_volBall | (intros; apply GlobalTheory.SepReal.powInt_of_volBall <;> assumption)
