import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsUniqueIsWeierstrassPSeries
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddThetaFunctionExistenceUniqueness
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableSqTh
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.EvenTheta
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsUniqueIsWeierstrassPSeries.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.existsUnique_isWeierstrassPSeries : ∀ (K : Type) [Field K] [CharZero K] (a b : K), ∃! P : PowerSeries K, IsWpSer a b P := by
  first | exact @GlobalTheory.WpSeries.existsUnique_isWpSer | exact GlobalTheory.WpSeries.existsUnique_isWpSer | (intros; apply GlobalTheory.WpSeries.existsUnique_isWpSer <;> assumption)
