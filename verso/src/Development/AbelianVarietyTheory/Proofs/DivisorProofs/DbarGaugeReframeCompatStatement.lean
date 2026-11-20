import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarGaugeReframeCompat
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionForm.Gauge.dbarV_gauge` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDbarGaugeReframeCompat.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.dbar_gauge_reframe_compat : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g n : ℕ} (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g) (s : Pt E g → Ext (n + n + g)), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → DifferentiableOn ℝ s (cov B g) → ∀ P ∈ cov B g, dbarV (gauge n τ γ s) P = frameAt n τ γ P.1 (dbarV s (reframe τ γ P)) := by
  first | exact @GlobalTheory.TorsionForm.Gauge.dbarV_gauge | exact GlobalTheory.TorsionForm.Gauge.dbarV_gauge | (intros; apply GlobalTheory.TorsionForm.Gauge.dbarV_gauge <;> assumption)
