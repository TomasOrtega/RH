import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.WeilOrthogonalGroupInvariance
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=CompanionTheory%2FSpectralGeometry%2FLocalGlobalProofs%2FAdelicAnalysis%2FWeilOrthogonalGroupInvariance.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.weil_orthogonal_group_invariance : ∀ (R : Type) [CommRing R] [TopologicalSpace R] [MeasurableSpace R] (ι : Type) [Fintype ι] [DecidableEq ι] (ψ : AddChar R ℂ) (h : R) (B : Matrix ι ι R) (μ : Measure (ι → R)), NAQuad ψ h B μ → ∀ g : Matrix ι ι R, IsUnit g.det → gᵀ * B * g = B → Measure.map (fun x => g *ᵥ x) μ = μ ∧ ∀ φ : (ι → R) → ℂ, SB φ → SB (fun x => φ (g *ᵥ x)) ∧ ∀ y, fou (chiB ψ B) μ (fun x => φ (g *ᵥ x)) y = fou (chiB ψ B) μ φ (g *ᵥ y) := by
  first | exact @GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas | exact GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas | (intros; apply GlobalTheory.CompanionTheory.SW.Core.OrthMeas.orth_meas <;> assumption)
