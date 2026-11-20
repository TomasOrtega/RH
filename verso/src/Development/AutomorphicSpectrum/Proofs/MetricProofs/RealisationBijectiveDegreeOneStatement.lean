import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RealisationBijectiveDegreeOne
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsFibreChartIff
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FRealisationBijectiveDegreeOne.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.realisation_bijective_degree_one : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (D : ℕ) (σ : Type) (S : AnSys D σ) (P : Ideal (MRing ι)) (Re : Realis S P), Re.deg = 1 → Re.br = ∅ → Function.Bijective Re.π := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one | exact GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib.realis_bijective_of_degree_one <;> assumption)
