import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeSquareZeroLiftsOfDeRhamCohomology
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAbelianSchemeSquareZeroLiftsOfDeRhamCohomology.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.abelianSchemeSquareZeroLifts_of_deRhamCohomology : AbelianHodgeDeRham → AbelianSchemeLifts := by
  first | exact @GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham | exact GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham | (intros; apply GlobalTheory.LiftSys.abelianSchemeLifts_of_abelianHodgeDeRham <;> assumption)
