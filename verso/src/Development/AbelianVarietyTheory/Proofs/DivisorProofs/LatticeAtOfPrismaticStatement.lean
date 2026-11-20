import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeAtOfPrismatic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EigWhole.latAt_onObj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLatticeAtOfPrismatic.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.lattice_at_of_prismatic : Hypotheses2 → HypothesesH → RegularAlteration → ScholzeWeinsteinB → PrismaticDieudonnePerfd → OnObj fun _ O _ _ _ _ => LatAt O.Y := by
  first | exact @GlobalTheory.EigWhole.latAt_onObj | exact GlobalTheory.EigWhole.latAt_onObj | (intros; apply GlobalTheory.EigWhole.latAt_onObj <;> assumption)
