import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTwoTorsionCMPointAllConjugates
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TwoTorsionPt.exists_point` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsTwoTorsionCMPointAllConjugates.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.exists_twoTorsionCMPoint_all_conjugates : ∀ D : D7, t0Ex D := by
  first | exact @GlobalTheory.TwoTorsionPt.exists_point | exact GlobalTheory.TwoTorsionPt.exists_point | (intros; apply GlobalTheory.TwoTorsionPt.exists_point <;> assumption)
