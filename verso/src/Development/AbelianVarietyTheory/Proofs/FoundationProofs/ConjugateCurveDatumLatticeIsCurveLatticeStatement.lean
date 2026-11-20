import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjugateCurveDatumLatticeIsCurveLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConjCurve.galCurve_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FConjugateCurveDatumLatticeIsCurveLattice.lean&line=232#L232)
-/
theorem _root_.GlobalTheory.T.conjugate_curveDatum_lattice_isCurveLattice : ∀ D : D7, galCurve D := by
  first | exact @GlobalTheory.ConjCurve.galCurve_holds | exact GlobalTheory.ConjCurve.galCurve_holds | (intros; apply GlobalTheory.ConjCurve.galCurve_holds <;> assumption)
