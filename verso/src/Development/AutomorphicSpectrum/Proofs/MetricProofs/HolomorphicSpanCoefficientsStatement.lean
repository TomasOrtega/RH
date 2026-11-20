import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.HolomorphicSpanCoefficients
import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange.log_gram_frame_change` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FMetricProofs%2FHolomorphicSpanCoefficients.lean&line=119#L119)
-/
theorem _root_.GlobalTheory.T.holomorphic_span_coefficients : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (n m : ℕ) (W : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g Λ) (b c : Fin m → (Fin n → ℂ) → Fin g → ℂ) (t₀ : Fin n → ℂ), IsOpen W → t₀ ∈ W → (∀ i, DifferentiableOn ℂ (b i) W) → (∀ i, DifferentiableOn ℂ (c i) W) → (∀ t ∈ W, LinearIndependent ℂ fun i => b i t) → (∀ t ∈ W, ∀ i, c i t ∈ Submodule.span ℂ (Set.range fun j => b j t)) → LinearIndependent ℂ (fun i => c i t₀) → ∃ V : Set (Fin n → ℂ), IsOpen V ∧ t₀ ∈ V ∧ V ⊆ W ∧ ∃ G : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ G V ∧ ∀ t ∈ V, LinearIndependent ℂ (fun i => c i t) ∧ Real.log ((R t).gram fun i => c i t).det.re = Real.log ((R t).gram fun i => b i t).det.re + (G t).re := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange.log_gram_frame_change | exact GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange.log_gram_frame_change | (intros; apply GlobalTheory.CompanionTheory.Ar.Cusp.FrameChange.log_gram_frame_change <;> assumption)
