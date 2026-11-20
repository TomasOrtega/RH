import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ContinuousCuspNormFamily
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.NzCont.continuous_nz` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FContinuousCuspNormFamily.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.continuous_cusp_norm_family : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (X : Type) [TopologicalSpace X] (R : X → RiemLat E g Λ) (σ : Ψ → (𝓞 E →+* ℂ)) (I : Submodule (𝓞 E) Λ), (∀ v, Continuous fun x => (R x).P v) → (Continuous fun x => (R x).Hm) → Continuous fun x => (R x).nz σ I := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.NzCont.continuous_nz | exact GlobalTheory.CompanionTheory.Ar.Cusp.NzCont.continuous_nz | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.NzCont.continuous_nz <;> assumption)
