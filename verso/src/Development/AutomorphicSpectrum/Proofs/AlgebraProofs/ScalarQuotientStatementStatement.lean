import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ScalarQuotientStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsBundles
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FAlgebraProofs%2FScalarQuotientStatement.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.scalar_quotient_statement : GroundTheory.Heights₂.Heights.NumbersDVR.ScalarQuotient.Statement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main | exact GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ScalarFlags.main <;> assumption)
