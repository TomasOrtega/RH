import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasIntegralEqChartDensityIntegral
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HSAmp.VolDens.meas_integral_in_chart` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMeasIntegralEqChartDensityIntegral.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.meas_integral_eq_chartDensity_integral : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (σ : k →+* ℂ) (ω : VolDens p σ D) (c : AlgChart p σ D) (S : Set (CxPts p σ)) (F : CxPts p σ → ℝ), MeasurableSet S → S ⊆ c.e.source → Continuous F → ω.meas S = ∫⁻ v in c.e '' S, ENNReal.ofReal (ω.dens c (c.e.symm v)) ∧ ∫ y in S, F y ∂ω.meas = ∫ v in c.e '' S, F (c.e.symm v) * ω.dens c (c.e.symm v) := by
  first | exact @GlobalTheory.HSAmp.VolDens.meas_integral_in_chart | exact GlobalTheory.HSAmp.VolDens.meas_integral_in_chart | (intros; apply GlobalTheory.HSAmp.VolDens.meas_integral_in_chart <;> assumption)
