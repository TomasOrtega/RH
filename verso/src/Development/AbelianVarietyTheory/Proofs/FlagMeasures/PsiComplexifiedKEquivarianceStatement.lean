import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dec.Equivar.psEquiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPsiComplexifiedKEquivariance.lean&line=225#L225)
-/
theorem _root_.GlobalTheory.T.psi_complexifiedK_equivariance : PsEquiv := by
  first | exact @GlobalTheory.Dec.Equivar.psEquiv | exact GlobalTheory.Dec.Equivar.psEquiv | (intros; apply GlobalTheory.Dec.Equivar.psEquiv <;> assumption)
