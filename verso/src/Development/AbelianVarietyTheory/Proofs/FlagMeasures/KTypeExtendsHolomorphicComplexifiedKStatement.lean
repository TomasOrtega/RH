import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.KTypeExtendsHolomorphicComplexifiedK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
open GlobalTheory.Dec
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Dec.TauExt.tauExists` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FKTypeExtendsHolomorphicComplexifiedK.lean&line=115#L115)
-/
theorem _root_.GlobalTheory.T.kType_extends_holomorphic_complexifiedK : TauExists := by
  first | exact @GlobalTheory.Dec.TauExt.tauExists | exact GlobalTheory.Dec.TauExt.tauExists | (intros; apply GlobalTheory.Dec.TauExt.tauExists <;> assumption)
