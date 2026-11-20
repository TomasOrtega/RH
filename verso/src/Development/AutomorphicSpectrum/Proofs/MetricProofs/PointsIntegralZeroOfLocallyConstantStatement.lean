import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.PointsIntegralZeroOfLocallyConstant
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsPieceDegree
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsEmbeddingPieces
import GroundTheory.HeightsAndTheta.Heights.Intersections.Statements
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsPushDown
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry Filter Topology NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FPointsIntegralZeroOfLocallyConstant.lean&line=79#L79)
-/
theorem _root_.GlobalTheory.T.points_integral_zero_of_locally_constant : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (e : ℕ) (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) (g : ((Σ k, ι k) → ℂ) → ℝ) (j : Fin e), (∀ z ∈ mcPts P, ∃ c : ℝ, φ j =ᶠ[𝓝 z] fun _ => c) → ptsIntegral P φ g = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | exact GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.ptsIntegral_eq_zero_of_locConst <;> assumption)
