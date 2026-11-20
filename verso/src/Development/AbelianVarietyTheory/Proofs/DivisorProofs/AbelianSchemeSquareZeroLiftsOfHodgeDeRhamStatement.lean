import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfHodgeDeRham
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeSquareZeroLiftsOfHodgeDeRham.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.abelianSchemeSquareZeroLifts_of_hodgeDeRham : CrystallineSmoothLift → AbelianHodgeDeRham → AbelianSchemeLifts := by
  first | exact @GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham | exact GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham | (intros; apply GlobalTheory.LiftSys.abelianSchemeLifts_of_hodgeDeRham <;> assumption)
