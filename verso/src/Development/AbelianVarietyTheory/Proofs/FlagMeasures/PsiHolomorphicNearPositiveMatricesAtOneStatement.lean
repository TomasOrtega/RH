import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiHolomorphicNearPositiveMatricesAtOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dec.psBasic` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPsiHolomorphicNearPositiveMatricesAtOne.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.psi_holomorphic_near_positive_matrices_at_one : PsBasic := by
  first | exact @GlobalTheory.Dec.psBasic | exact GlobalTheory.Dec.psBasic | (intros; apply GlobalTheory.Dec.psBasic <;> assumption)
