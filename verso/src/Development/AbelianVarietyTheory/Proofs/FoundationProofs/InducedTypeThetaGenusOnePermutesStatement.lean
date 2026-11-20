import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.InducedType.induced_type` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FInducedTypeThetaGenusOnePermutes.lean&line=74#L74)
-/
theorem _root_.GlobalTheory.T.inducedType_thetaGenusOne_permutes : ∀ D : D7, admG1 D ∧ EmbeddingPermutesTypes D := by
  first | exact @GlobalTheory.InducedType.induced_type | exact GlobalTheory.InducedType.induced_type | (intros; apply GlobalTheory.InducedType.induced_type <;> assumption)
