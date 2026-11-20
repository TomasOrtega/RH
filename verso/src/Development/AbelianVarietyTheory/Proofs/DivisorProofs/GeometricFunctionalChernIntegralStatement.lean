import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricFunctionalChernIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeometricFunctionalChernIntegral.lean&line=184#L184)
-/
theorem _root_.GlobalTheory.T.geometric_functional_chern_integral : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (ι : Type) [Fintype ι] (L : ι → HermLB p) (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ),
    IsGeoFun L D Ψ → ∀ G : MvPolynomial ι ℝ, G.IsHomogeneous D →
      Ψ G = ∑ᶠ σ : k →+* ℂ, (hX.atlas σ).integral (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) G) := by
  first | exact @GlobalTheory.LineForm.GeoInt.geoFun_eq_integral | exact GlobalTheory.LineForm.GeoInt.geoFun_eq_integral | (intros; apply GlobalTheory.LineForm.GeoInt.geoFun_eq_integral <;> assumption)
