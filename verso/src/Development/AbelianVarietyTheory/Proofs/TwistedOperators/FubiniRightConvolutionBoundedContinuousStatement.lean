import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FubiniRightConvolutionBoundedContinuous
open MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.fubini_right_convolution_bounded_continuous` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFubiniRightConvolutionBoundedContinuous.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.integral_fundamentalDomain_convolution_comm_of_bounded : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] {H : Subgroup G} (μ : Measure G) (𝓕 : Set G), μ 𝓕 < ⊤ → ∀ (m : Measure H) [SFinite m] (α : H → ℂ), Integrable α m → ∀ (ψ φ : G → ℂ), Continuous ψ → Continuous φ → ∀ (A B : ℝ), (∀ g, ‖ψ g‖ ≤ A) → (∀ g, ‖φ g‖ ≤ B) → IntegrableOn (fun x => ψ x * ∫ h, α h * φ (x * (h : G)) ∂m) 𝓕 μ ∧ Integrable (fun h : H => α h * ∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) m ∧ ∫ x in 𝓕, ψ x * (∫ h, α h * φ (x * (h : G)) ∂m) ∂μ = ∫ h, α h * (∫ x in 𝓕, ψ x * φ (x * (h : G)) ∂μ) ∂m := by
  first | exact @GlobalTheory.fubini_right_convolution_bounded_continuous | exact GlobalTheory.fubini_right_convolution_bounded_continuous | (intros; apply GlobalTheory.fubini_right_convolution_bounded_continuous <;> assumption)
