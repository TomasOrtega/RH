import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntersectionNumberPolynomial
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsPresents
open CategoryTheory AlgebraicGeometry TopologicalSpace MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.Published.ArDegreeModel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FIntersectionNumberPolynomial.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.intersection_number_polynomial : ∀ (Y : Var ℂ) (Δ Δ₀ : Y.Dv), ∃ Q : Polynomial ℝ, ∀ m : ℕ, ((Y.inter fun _ => Δ + m • Δ₀ : ℤ) : ℝ) = Q.eval (m : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial | exact GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial | (intros; apply GlobalTheory.CompanionTheory.ChernPoly.inter_add_nsmul_polynomial <;> assumption)
