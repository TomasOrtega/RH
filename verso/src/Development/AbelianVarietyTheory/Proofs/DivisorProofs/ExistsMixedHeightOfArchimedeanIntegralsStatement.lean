import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMixedHeightOfArchimedeanIntegrals
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MixHt.exists_isMix_of_arch` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsMixedHeightOfArchimedeanIntegrals.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_mixedHeight_of_archimedean_integrals : ArchInteg → ArchRecip → (∀ (k : Type) [CommRing k] (Y : Scheme.{0}) (q : Y ⟶ Sp k), IsAmb q → ∀ m : ℕ, ∃ T, IsMix q m T) := by
  first | exact @GlobalTheory.MixHt.exists_isMix_of_arch | exact GlobalTheory.MixHt.exists_isMix_of_arch | (intros; apply GlobalTheory.MixHt.exists_isMix_of_arch <;> assumption)
