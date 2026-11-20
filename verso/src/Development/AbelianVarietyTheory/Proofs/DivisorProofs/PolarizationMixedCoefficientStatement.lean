import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationMixedCoefficient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetCoef.coeff_compare` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPolarizationMixedCoefficient.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.polarization_mixed_coefficient : ∀ (R : Type) [CommRing R] [Algebra ℝ R] (Λ : R →ₗ[ℝ] ℝ) (a b : R) (f e : ℕ) (Θ N : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ) (s : ℝ), (∀ t : ℝ, Λ ((a + t • b) ^ (f + e)) = s * (Θ + (t : ℂ) • N).det.re) → ((f + e).choose e : ℝ) * Λ (a ^ f * b ^ e) = s * (N.adjugate * Θ).trace.re := by
  first | exact @GlobalTheory.DetCoef.coeff_compare | exact GlobalTheory.DetCoef.coeff_compare | (intros; apply GlobalTheory.DetCoef.coeff_compare <;> assumption)
