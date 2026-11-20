import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GaloisTaylorSeriesCanonicalOddThetaAll
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SigmaConj.galSg_all` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGaloisTaylorSeriesCanonicalOddThetaAll.lean&line=623#L623)
-/
theorem _root_.GlobalTheory.T.galois_taylorSeries_canonicalOddTheta_all : ∀ D : D7, galSg D := by
  first | exact @GlobalTheory.SigmaConj.galSg_all | exact GlobalTheory.SigmaConj.galSg_all | (intros; apply GlobalTheory.SigmaConj.galSg_all <;> assumption)
