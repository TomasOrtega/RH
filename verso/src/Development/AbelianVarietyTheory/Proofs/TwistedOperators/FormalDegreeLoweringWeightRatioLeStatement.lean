import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FormalDegreeLoweringWeightRatioLe
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.OneMemNbh
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteBranchingUpq
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Ell
open scoped InnerProductSpace
open GlobalTheory.SepReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFormalDegreeLoweringWeightRatioLe.lean&line=188#L188)
-/
theorem _root_.GlobalTheory.T.formalDegree_loweringWeight_ratio_le : DegRatio := by
  first | exact @GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds | exact GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds | (intros; apply GlobalTheory.SepReal.FormalDegreeRatio.degRatio_holds <;> assumption)
