import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimitiveDegreeTwoExtension
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveStructureSheafDegTwoVanish
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianUnobstructed
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrimitiveDegreeTwoExtension.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.primitive_degree_two_extension : PrimitiveStructureSheafDegTwoVanish → PrimitiveExtendedDegTwoVanish := by
  first | exact @GlobalTheory.Obs.primE2_of_primO2 | exact GlobalTheory.Obs.primE2_of_primO2 | (intros; apply GlobalTheory.Obs.primE2_of_primO2 <;> assumption)
