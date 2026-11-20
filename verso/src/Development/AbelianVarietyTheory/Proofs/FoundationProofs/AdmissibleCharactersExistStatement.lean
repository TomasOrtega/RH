import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleCharactersExist
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TripleIntertwiner.triple_constant` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FAdmissibleCharactersExist.lean&line=108#L108)
-/
theorem _root_.GlobalTheory.T.admissible_characters_exist : ∀ D : D7, GaussSumTripleConstant D := by
  first | exact @GlobalTheory.TripleIntertwiner.triple_constant | exact GlobalTheory.TripleIntertwiner.triple_constant | (intros; apply GlobalTheory.TripleIntertwiner.triple_constant <;> assumption)
