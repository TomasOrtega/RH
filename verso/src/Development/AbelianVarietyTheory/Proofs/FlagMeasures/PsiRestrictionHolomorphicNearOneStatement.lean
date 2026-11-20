import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiRestrictionHolomorphicNearOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FPsiRestrictionHolomorphicNearOne.lean&line=223#L223)
-/
theorem _root_.GlobalTheory.T.psi_restriction_holomorphic_near_one : PsLocal := by
  first | exact @GlobalTheory.Dec.psLocal | exact GlobalTheory.Dec.psLocal | (intros; apply GlobalTheory.Dec.psLocal <;> assumption)
