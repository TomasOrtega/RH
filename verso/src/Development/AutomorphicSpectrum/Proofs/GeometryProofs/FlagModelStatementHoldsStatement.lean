import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagModelStatementHolds
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlagModelStatement
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FFlagModelStatementHolds.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.FlagModelStatement_holds : FlagModelStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel | exact GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel | (intros; apply GlobalTheory.CompanionTheory.Ar.FlagModel.flagModel <;> assumption)
