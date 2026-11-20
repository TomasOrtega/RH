import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslationIntertwinerUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FThetaTranslationIntertwinerUnitary.lean&line=183#L183)
-/
theorem _root_.GlobalTheory.T.intertwinerUnitary_all : ∀ D : D7, IntertwinerUnitary D := by
  first | exact @GlobalTheory.theta_translation_intertwiner_unitary | exact GlobalTheory.theta_translation_intertwiner_unitary | (intros; apply GlobalTheory.theta_translation_intertwiner_unitary <;> assumption)
