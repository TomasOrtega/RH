import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalStarComplexMultiplicationPoints
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGalStarComplexMultiplicationPoints.lean&line=286#L286)
-/
theorem _root_.GlobalTheory.T.galStar_complexMultiplication_points : ∀ D : D7, galStar D := by
  first | exact @GlobalTheory.ConjPoint.galStar_holds | exact GlobalTheory.ConjPoint.galStar_holds | (intros; apply GlobalTheory.ConjPoint.galStar_holds <;> assumption)
