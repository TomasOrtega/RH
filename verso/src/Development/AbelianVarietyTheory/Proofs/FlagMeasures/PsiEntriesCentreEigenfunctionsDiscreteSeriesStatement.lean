import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesCentreEigenfunctionsDiscreteSeries
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dec.PsiEig.psiEigen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPsiEntriesCentreEigenfunctionsDiscreteSeries.lean&line=726#L726)
-/
theorem _root_.GlobalTheory.T.psiEntries_centreEigenfunctions_discreteSeries : PsiEigen := by
  first | exact @GlobalTheory.Dec.PsiEig.psiEigen | exact GlobalTheory.Dec.PsiEig.psiEigen | (intros; apply GlobalTheory.Dec.PsiEig.psiEigen <;> assumption)
