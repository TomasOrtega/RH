import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FderivDetEqTraceAdjugate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtConst
open Matrix GlobalTheory.MatDeriv
open scoped Topology

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MatDeriv.jacobi_fderiv_det` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFderivDetEqTraceAdjugate.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.fderiv_det_eq_trace_adjugate : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ} (B : E → Matrix (Fin n) (Fin n) ℂ) (w : E), (∀ a b, DifferentiableAt ℝ (fun w' => B w' a b) w) → DifferentiableAt ℝ (fun w' => (B w').det) w ∧ ∀ ξ : E, fderiv ℝ (fun w' => (B w').det) w ξ = ((B w).adjugate * dMat B w ξ).trace := by
  first | exact @GlobalTheory.MatDeriv.jacobi_fderiv_det | exact GlobalTheory.MatDeriv.jacobi_fderiv_det | (intros; apply GlobalTheory.MatDeriv.jacobi_fderiv_det <;> assumption)
