import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatrixLengthExistsOfElementaryDivisors
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InertZeta.fracExists_of_smith` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FMatrixLengthExistsOfElementaryDivisors.lean&line=58#L58)
-/
theorem _root_.GlobalTheory.T.matrixLengthExists_of_elementaryDivisors : Smith → FracExists := by
  first | exact @GlobalTheory.InertZeta.fracExists_of_smith | exact GlobalTheory.InertZeta.fracExists_of_smith | (intros; apply GlobalTheory.InertZeta.fracExists_of_smith <;> assumption)
