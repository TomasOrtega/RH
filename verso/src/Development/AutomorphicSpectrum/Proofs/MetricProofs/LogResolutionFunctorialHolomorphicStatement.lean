import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FLogResolutionFunctorialHolomorphic.lean&line=252#L252)
-/
theorem _root_.GlobalTheory.T.log_resolution_functorial_holomorphic : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (κ : K → K') (v : (Σ k, ι k) → (Σ k, ι' k)) (P : Ideal (MRing ι)) (P' J' : Ideal (MRing ι')) (D D' : ℕ) (R : AnLogRes P ⊤ D) (R' : AnLogRes P' J' D'), IsBlockMap κ v → P ≤ imageZ v P' → ∃ h : R'.X → R.X, HoloMap R'.A R.A h ∧ ∀ x, SameOrbit (R.lift (h x) (h x)) (R'.lift x x ∘ v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj | exact GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj <;> assumption)
