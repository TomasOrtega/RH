import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralMatrixFirstRowColumn
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLintegralMatrixFirstRowColumn.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.lintegral_matrix_first_row_column : ∀ (k : Type) [MeasurableSpace k] (ν : Measure k) [SigmaFinite ν] (n : ℕ) (F : Matrix (Fin (n + 1)) (Fin (n + 1)) k → ℝ≥0∞),
    ∫⁻ X, F X ∂(volM ν (Fin (n + 1)) (Fin (n + 1))) ≤
      ∫⁻ M, ∫⁻ v, ∫⁻ u, ∫⁻ x, F (Matrix.of (Fin.cons (Fin.cons x u : Fin (n + 1) → k) (fun i => (Fin.cons (v i) (M i) : Fin (n + 1) → k))))
        ∂ν ∂(Measure.pi fun _ : Fin n => ν) ∂(Measure.pi fun _ : Fin n => ν) ∂(volM ν (Fin n) (Fin n)) := by
  first | exact @GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner | exact GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner | (intros; apply GlobalTheory.KSplit.CornerFubini.lintegral_volM_le_corner <;> assumption)
