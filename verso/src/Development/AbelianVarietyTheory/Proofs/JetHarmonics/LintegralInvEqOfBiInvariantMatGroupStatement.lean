import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.LintegralInvEqOfBiInvariantMatGroup
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HaarInversion.lintegral_inv_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FLintegralInvEqOfBiInvariantMatGroup.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.lintegral_inv_eq_of_biInvariant_matGroup : ∀ (m : ℕ) (S : Set (Matrix (Fin m) (Fin m) ℂ)) (μ : Measure (PI.MtM m)), PI.IsMatGroup S → PI.IsHaarOnM S μ → PI.IsRightInvM S μ → ∀ f : PI.MtM m → ℝ≥0∞, Measurable f → ∫⁻ s, f (fun i j => (Matrix.of s)⁻¹ i j) ∂μ = ∫⁻ s, f s ∂μ := by
  first | exact @GlobalTheory.HaarInversion.lintegral_inv_eq | exact GlobalTheory.HaarInversion.lintegral_inv_eq | (intros; apply GlobalTheory.HaarInversion.lintegral_inv_eq <;> assumption)
