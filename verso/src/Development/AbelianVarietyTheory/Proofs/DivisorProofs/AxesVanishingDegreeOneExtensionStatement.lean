import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingDegreeOneExtension
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
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAxesVanishingDegreeOneExtension.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.axes_vanishing_degree_one_extension : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  first | exact @GlobalTheory.Obs.axesE1_of_axesO1 | exact GlobalTheory.Obs.axesE1_of_axesO1 | (intros; apply GlobalTheory.Obs.axesE1_of_axesO1 <;> assumption)
