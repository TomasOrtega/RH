import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EssFiniteTypeOfLocalRingOfVarietyPoint
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalization
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEssFiniteTypeOfLocalRingOfVarietyPoint.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.essFiniteType_of_localRingOfVarietyPoint : ∀ {K : Type} [Field K] [Algebra ℂ K] (R : Subring K),
  IsLocModel (algebraMap ℂ K) R → Algebra.EssFiniteType ℂ K := by
  first | exact @GlobalTheory.essFiniteType_of_isLocModel | exact GlobalTheory.essFiniteType_of_isLocModel | (intros; apply GlobalTheory.essFiniteType_of_isLocModel <;> assumption)
