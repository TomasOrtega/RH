import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithIntersectionNumberExistsOfMixedHeights
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MixHt.arFormExists_of_isMix` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FArithIntersectionNumberExistsOfMixedHeights.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.arithIntersectionNumber_exists_of_mixedHeights : ArchInteg → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) → GlobalTheory.Published.ArFormExists := by
  first | exact @GlobalTheory.MixHt.arFormExists_of_isMix | exact GlobalTheory.MixHt.arFormExists_of_isMix | (intros; apply GlobalTheory.MixHt.arFormExists_of_isMix <;> assumption)
