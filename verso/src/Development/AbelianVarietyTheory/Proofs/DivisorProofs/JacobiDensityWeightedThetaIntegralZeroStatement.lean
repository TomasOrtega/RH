import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JacobiDensityWeightedThetaIntegralZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
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
Apply `GlobalTheory.MixDens.Canon.integral_jacDens_mul_theta` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJacobiDensityWeightedThetaIntegralZero.lean&line=196#L196)
-/
theorem _root_.GlobalTheory.T.jacobi_density_weighted_theta_integral_zero : ∀ (m : ℕ) (G K : Matrix (Fin m) (Fin m) ℂ), G.PosDef → K.IsHermitian → ∫ n : Low m → ℂ, jacDens G n * ∑ i : Fin m, ((m : ℝ) - 1 - 2 * (i : ℕ)) * theta G K n i = 0 := by
  first | exact @GlobalTheory.MixDens.Canon.integral_jacDens_mul_theta | exact GlobalTheory.MixDens.Canon.integral_jacDens_mul_theta | (intros; apply GlobalTheory.MixDens.Canon.integral_jacDens_mul_theta <;> assumption)
