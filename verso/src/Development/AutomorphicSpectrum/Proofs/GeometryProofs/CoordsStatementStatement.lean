import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsStatement
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FCoordsStatement.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.coords_statement : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement := by
  first | exact @GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side | exact GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side | (intros; apply GlobalTheory.CompanionTheory.Geo.SncCoordsSide.coordsStatement_side <;> assumption)
