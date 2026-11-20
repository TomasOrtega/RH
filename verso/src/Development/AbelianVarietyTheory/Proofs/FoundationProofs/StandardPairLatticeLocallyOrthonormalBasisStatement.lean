import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardPairLatticeLocallyOrthonormalBasis
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FStandardPairLatticeLocallyOrthonormalBasis.lean&line=420#L420)
-/
theorem _root_.GlobalTheory.T.standardPairLattice_locally_orthonormal_basis : ∀ D : D7, odd1 D := by
  first | exact @GlobalTheory.OddGenus.odd_one | exact GlobalTheory.OddGenus.odd_one | (intros; apply GlobalTheory.OddGenus.odd_one <;> assumption)
