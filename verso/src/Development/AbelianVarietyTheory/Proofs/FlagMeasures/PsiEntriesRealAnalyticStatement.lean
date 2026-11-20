import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiEntriesRealAnalytic
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Dec.psiAnalytic | exact GlobalTheory.Dec.psiAnalytic | (intros; apply GlobalTheory.Dec.psiAnalytic <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.psi_entries_real_analytic : PsiAnalytic := by
  first | exact @GlobalTheory.Dec.psiAnalytic | exact GlobalTheory.Dec.psiAnalytic | (intros; apply GlobalTheory.Dec.psiAnalytic <;> assumption)
