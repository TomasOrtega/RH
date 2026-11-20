import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousFirstMinimumFamily
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FContinuousFirstMinimumFamily.lean&line=148#L148)
-/
theorem _root_.GlobalTheory.T.continuous_first_minimum_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).lam1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum | exact GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.continuous_first_minimum <;> assumption)
