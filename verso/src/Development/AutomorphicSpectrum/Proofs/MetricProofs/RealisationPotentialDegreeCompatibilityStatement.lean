import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationPotentialDegreeCompatibility
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FRealisationPotentialDegreeCompatibility.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.realisation_potential_degree_compatibility : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), (∀ a t, 0 < t → t ≤ S.t₀ → SamePot Re.R.A Set.univ (potOf Re.R (Re.line a t)) ((S.potT a t).pullback Re.π Re.holo.1)) ∧ (∀ (w : Fin D → σ), ptsIntegral P (pot fun j => Re.ref (w j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ (∀ (w : Fin D → σ) (t : Fin D → ℝ), (∀ j, 0 < t j ∧ t j ≤ S.t₀) → ptsIntegral P (pot fun j => Re.line (w j) (t j)) (fun _ => 1) = Re.deg * S.degNum w) ∧ ∀ n : σ → ℤ, IsSmoothHerm (combLine Re.ref n) ∧ geomDeg P (combLine Re.ref n) D = Re.deg * eval (fun a => (n a : ℝ)) S.degPoly := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.re_pot | exact GlobalTheory.CompanionTheory.Ar.PB.re_pot | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.re_pot <;> assumption)
