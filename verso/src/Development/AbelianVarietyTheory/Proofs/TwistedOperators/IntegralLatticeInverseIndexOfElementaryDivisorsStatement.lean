import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralLatticeInverseIndexOfElementaryDivisors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertZeta.latIndex_of_smith` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIntegralLatticeInverseIndexOfElementaryDivisors.lean&line=138#L138)
-/
theorem _root_.GlobalTheory.T.integralLatticeInverseIndex_of_elementaryDivisors : Smith → LatIndex := by
  first | exact @GlobalTheory.InertZeta.latIndex_of_smith | exact GlobalTheory.InertZeta.latIndex_of_smith | (intros; apply GlobalTheory.InertZeta.latIndex_of_smith <;> assumption)
