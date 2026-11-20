import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.GeometricDegreeNonnegativePsh
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FGeometricDegreeNonnegativePsh.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.geometric_degree_nonnegative_psh : Inputs → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (Fl : Set σ), (∀ a ∈ Fl, ∀ t, IsPsh S.A ((S.potT a t).rsmul (-1)) ∧ IsPsh S.A (S.potT a t)) → Re.J = ⊤ → ∀ n : σ → ℤ, (∀ a ∉ Fl, 0 ≤ n a) → ∀ W : Ideal (MRing ι), IsArithVar W 2 → P ≤ W → 0 ≤ geomDeg W (combLine Re.ref n) 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.nonneg_degree_horizontal_curve | exact GlobalTheory.CompanionTheory.Ar.PB.nonneg_degree_horizontal_curve | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.nonneg_degree_horizontal_curve <;> assumption)
