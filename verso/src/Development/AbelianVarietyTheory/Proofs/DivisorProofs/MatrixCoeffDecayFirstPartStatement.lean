import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixCoeffDecayFirstPart
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RealMetaplecticRepresentation
open MeasureTheory GlobalTheory.RealWeil
open scoped SchwartzMap
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FMatrixCoeffDecayFirstPart.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.matrix_coeff_decay_first_part : ∀ (n : ℕ) (g g' : Sch (Fin n)) (N : ℕ), ∃ C : ℝ, ∀ w : Fin n ⊕ Fin n → ℝ, ‖∫ x, rhoFun w ⇑g x * starRingEnd ℂ (g' x)‖ * (1 + ‖pPart w‖) ^ N ≤ C := by
  first | exact @GlobalTheory.matrixCoeff_pPart_decay | exact GlobalTheory.matrixCoeff_pPart_decay | (intros; apply GlobalTheory.matrixCoeff_pPart_decay <;> assumption)
