import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoAnyRing
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasOpens
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Obs.primE2_any_ring` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrimitiveDegreeTwoAnyRing.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.primitive_degree_two_any_ring : PrimitiveExtendedDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primE2_any_ring | exact GlobalTheory.Obs.primE2_any_ring | (intros; apply GlobalTheory.Obs.primE2_any_ring <;> assumption)
