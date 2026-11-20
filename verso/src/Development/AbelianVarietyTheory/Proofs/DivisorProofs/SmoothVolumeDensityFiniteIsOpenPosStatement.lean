import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothVolumeDensityFiniteIsOpenPos
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSAmp.volDens_meas_finite_openPos` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothVolumeDensityFiniteIsOpenPos.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.smoothVolumeDensity_finite_isOpenPos : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D), IsFiniteMeasure ω.meas ∧ ω.meas.IsOpenPosMeasure := by
  first | exact @GlobalTheory.HSAmp.volDens_meas_finite_openPos | exact GlobalTheory.HSAmp.volDens_meas_finite_openPos | (intros; apply GlobalTheory.HSAmp.volDens_meas_finite_openPos <;> assumption)
