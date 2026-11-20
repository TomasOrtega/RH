import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrderedCechToCatCochainsOneCoboundaryComm
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOrderedCechToCatCochainsOneCoboundaryComm.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.orderedCech_cochainsOne_coboundary_comm : ∀ {κ : Type} [LinearOrder κ] {R : Type} [CommRing R] (F : (NE κ)ᵒᵖ ⥤ CommAlgCat.{0} R) (c : CC F 1), d1 F (e1 F c) = e2 F (δ F 1 c) := by
  first | exact @GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm | exact GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm | (intros; apply GlobalTheory.CechPosetDegreeOne.orderedCechToCatCochainsOne_coboundary_comm <;> assumption)
