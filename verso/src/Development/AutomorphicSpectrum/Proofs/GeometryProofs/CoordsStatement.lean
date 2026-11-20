import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HasSncCoordsOfLocal
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R ReciprocityTheory.ChartRestriction.G.Geo.ResK

namespace GlobalTheory.CompanionTheory.Geo.SncCoordsSide

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Geo.SncCoords.coordsStatement`.
-/
theorem coordsStatement_side : ReciprocityTheory.ChartRestriction.G.Geo.ResK.CoordsStatement :=
  GlobalTheory.CompanionTheory.Geo.SncCoords.coordsStatement

end GlobalTheory.CompanionTheory.Geo.SncCoordsSide
