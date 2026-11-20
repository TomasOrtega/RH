import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MinimalSiegelCompactificationExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NotSymEOfNe
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifAlong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMinimalSiegelCompactificationExists.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.minimalSiegelCompactification_exists : GlobalTheory.SiegJoin.MinSt5 := by
  first | exact @GlobalTheory.SiegMinTop.minSt5 | exact GlobalTheory.SiegMinTop.minSt5 | (intros; apply GlobalTheory.SiegMinTop.minSt5 <;> assumption)
