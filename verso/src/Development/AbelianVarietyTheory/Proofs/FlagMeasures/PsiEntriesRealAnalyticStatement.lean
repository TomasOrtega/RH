import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesRealAnalytic
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dec.psiAnalytic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPsiEntriesRealAnalytic.lean&line=282#L282)
-/
theorem _root_.GlobalTheory.T.psi_entries_real_analytic : PsiAnalytic := by
  first | exact @GlobalTheory.Dec.psiAnalytic | exact GlobalTheory.Dec.psiAnalytic | (intros; apply GlobalTheory.Dec.psiAnalytic <;> assumption)
