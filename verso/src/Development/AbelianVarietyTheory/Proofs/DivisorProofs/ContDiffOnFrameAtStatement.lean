import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnFrameAt
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAddVectorScalar
open Matrix MeasureTheory Set Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.Gauge
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionForm.Gauge.contDiffOn_frameAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContDiffOnFrameAt.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.contDiffOn_frameAt_of_isPeriodMap : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {g : ℕ} (n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (γ : Sp g), IsPeriodMap B τ → IsPeriodMap B (fun b => moeb γ (τ b)) → ContDiffOn ℝ ∞ (fun b => frameAt n τ γ b) B := by
  first | exact @GlobalTheory.TorsionForm.Gauge.contDiffOn_frameAt | exact GlobalTheory.TorsionForm.Gauge.contDiffOn_frameAt | (intros; apply GlobalTheory.TorsionForm.Gauge.contDiffOn_frameAt <;> assumption)
