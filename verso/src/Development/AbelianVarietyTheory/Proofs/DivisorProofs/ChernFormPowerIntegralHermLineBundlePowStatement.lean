import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormPowerIntegralHermLineBundlePow
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FChernFormPowerIntegralHermLineBundlePow.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.chernFormPowerIntegral_hermLineBundle_pow : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (L : HermLB p) (n : ℕ) (w : ∀ σ, CxPts p σ → ℝ), chInt (L.pow n) D w = (n : ℝ) ^ D * chInt L D w := by
  first | exact @GlobalTheory.HSAmp.chInt_pow | exact GlobalTheory.HSAmp.chInt_pow | (intros; apply GlobalTheory.HSAmp.chInt_pow <;> assumption)
