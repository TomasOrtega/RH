import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaGaugeReframeCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNablaGaugeReframeCompat.lean&line=298#L298)
-/
theorem _root_.GlobalTheory.T.nabla_gauge_reframe_compat : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (h : Pt E g → ℝ) (β : Fin n → E) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) → DifferentiableOn ℝ s (cov B g) → ∀ P ∈ cov B g, nablaE τ (fun Q => h (reframe τ γ Q)) β (gauge n τ γ s) P = frameAt n τ γ P.1 (nablaE (fun b => moeb γ (τ b)) h β s (reframe τ γ P)) := by
  first | exact @GlobalTheory.TorsionForm.Gauge.NablaConj.nablaE_gauge | exact GlobalTheory.TorsionForm.Gauge.NablaConj.nablaE_gauge | (intros; apply GlobalTheory.TorsionForm.Gauge.NablaConj.nablaE_gauge <;> assumption)
