import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionDifferenceTelescopingIntegral
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FIntersectionDifferenceTelescopingIntegral.lean&line=143#L143)
-/
theorem _root_.GlobalTheory.T.intersection_difference_telescoping_integral : Inputs → ∀ (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) [Fintype σ] (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P) (t t' : ℝ) (w : Fin (D + 1) → σ), 0 < t → t ≤ S.t₀ → 0 < t' → t' ≤ S.t₀ → Re.num II t w - Re.num II t' w = ∑ r : Fin (D + 1), mInt S.A (fun i => S.potT (w (r.succAbove i)) (if r.succAbove i < r then t else t')) (fun x => S.phT (w r) t x - S.phT (w r) t' x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.num_sub_num | exact GlobalTheory.CompanionTheory.Ar.PB.num_sub_num | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.num_sub_num <;> assumption)
