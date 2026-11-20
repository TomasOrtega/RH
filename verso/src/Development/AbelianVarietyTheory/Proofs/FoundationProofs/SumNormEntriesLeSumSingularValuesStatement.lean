import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumNormEntriesLeSumSingularValues
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StarMulOfMemKc
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower GlobalTheory.CartanInt Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CartanInt.Frob.sum_norm_le_sum_singVal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSumNormEntriesLeSumSingularValues.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.sum_norm_entries_le_sum_singularValues : ∀ (p q : ℕ) (B : Matrix (Fin p) (Fin q) ℂ), ∑ i, ∑ j, ‖B i j‖ ≤ (((p + q : ℕ) : ℝ) + 1) / 2 * ∑ i ∈ Finset.range (min p q), singVal B i := by
  first | exact @GlobalTheory.CartanInt.Frob.sum_norm_le_sum_singVal | exact GlobalTheory.CartanInt.Frob.sum_norm_le_sum_singVal | (intros; apply GlobalTheory.CartanInt.Frob.sum_norm_le_sum_singVal <;> assumption)
