import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ResolutionStatementHolds
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FResolutionStatementHolds.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.resolution_statement_holds : ReciprocityTheory.ChartRestriction.G.Geo.ResBridgeStatement := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds | exact GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds | (intros; apply GlobalTheory.CompanionTheory.Ar.Link.resBridgeStatement_holds <;> assumption)
