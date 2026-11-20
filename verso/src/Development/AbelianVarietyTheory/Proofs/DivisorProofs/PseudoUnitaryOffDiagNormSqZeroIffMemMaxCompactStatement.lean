import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PseudoUnitaryOffDiagNormSqZeroIffMemMaxCompact
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPseudoUnitaryOffDiagNormSqZeroIffMemMaxCompact.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.pseudoUnitary_offDiag_norm_sq_zero_iff_mem_maxCompact : ∀ (n : ℕ) (ε : Fin n → Bool) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 = 0 ↔ g ∈ KG ε := by
  first | exact @GlobalTheory.offDiag_zero_iff_mem_K | exact GlobalTheory.offDiag_zero_iff_mem_K | (intros; apply GlobalTheory.offDiag_zero_iff_mem_K <;> assumption)
