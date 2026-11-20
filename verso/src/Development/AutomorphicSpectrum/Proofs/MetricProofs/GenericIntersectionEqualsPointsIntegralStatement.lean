import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GenericIntersectionEqualsPointsIntegral
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.curvatureIntegral_eq_genericIntersection` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FGenericIntersectionEqualsPointsIntegral.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.generic_intersection_equals_points_integral : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (I : IFamily ℚ ι), IsFieldIntersection I → ∀ (D : ℕ) (P : Ideal (MRing ι)) (L : Fin D → HermLine ι), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → ptsIntegral P (pot L) (fun _ => 1) = (I (P.map (MvPolynomial.map (Int.castRingHom ℚ))) D fun j => (L j).a : ℤ) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.curvatureIntegral_eq_genericIntersection | exact GlobalTheory.CompanionTheory.Ar.PB.curvatureIntegral_eq_genericIntersection | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.curvatureIntegral_eq_genericIntersection <;> assumption)
