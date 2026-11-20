import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalCompactificationPolarisedCharts
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SiegJoin.siegelToroidalPolCharts` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSiegelToroidalCompactificationPolarisedCharts.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.siegelToroidalCompactification_polarisedCharts : GlobalTheory.Published.SiegelToroidalPolCharts := by
  first | exact @GlobalTheory.SiegJoin.siegelToroidalPolCharts | exact GlobalTheory.SiegJoin.siegelToroidalPolCharts | (intros; apply GlobalTheory.SiegJoin.siegelToroidalPolCharts <;> assumption)
