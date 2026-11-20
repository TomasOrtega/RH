import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUnitaryClassRepTrivialAtCm
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsUnitaryClassRepTrivialAtCm.lean&line=385#L385)
-/
theorem _root_.GlobalTheory.T.exists_unitaryClass_rep_trivial_at_cm : ∀ D : D7, oddRep D := by
  first | exact @GlobalTheory.NormSum.exists_rep_trivial_at | exact GlobalTheory.NormSum.exists_rep_trivial_at | (intros; apply GlobalTheory.NormSum.exists_rep_trivial_at <;> assumption)
