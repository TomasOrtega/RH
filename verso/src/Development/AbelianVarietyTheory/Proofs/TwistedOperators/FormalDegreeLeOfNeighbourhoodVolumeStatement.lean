import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLeOfNeighbourhoodVolume
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepReal.degUpper_of` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFormalDegreeLeOfNeighbourhoodVolume.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.formalDegree_le_of_neighbourhoodVolume : LogNear → LieBound → VolBall → DegUpper := by
  first | exact @GlobalTheory.SepReal.degUpper_of | exact GlobalTheory.SepReal.degUpper_of | (intros; apply GlobalTheory.SepReal.degUpper_of <;> assumption)
