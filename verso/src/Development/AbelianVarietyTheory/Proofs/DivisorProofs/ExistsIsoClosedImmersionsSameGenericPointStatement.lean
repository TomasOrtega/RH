import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoClosedImmersionsSameGenericPoint
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsIsoClosedImmersionsSameGenericPoint.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.exists_iso_closedImmersions_same_genericPoint : ∀ (X Y Y' : Scheme.{0}) [IsIntegral Y] [IsIntegral Y'] (i : Y ⟶ X) (i' : Y' ⟶ X) [IsClosedImmersion i] [IsClosedImmersion i'], i (genericPoint Y) = i' (genericPoint Y') → ∃ g : Y' ⟶ Y, IsIso g ∧ g ≫ i = i' ∧ g (genericPoint Y') = genericPoint Y := by
  first | exact @GlobalTheory.iso_of_closedImmersion_genericPoint_eq | exact GlobalTheory.iso_of_closedImmersion_genericPoint_eq | (intros; apply GlobalTheory.iso_of_closedImmersion_genericPoint_eq <;> assumption)
