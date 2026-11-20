import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactPseudoUnitaryOffDiagNormSublevel
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsCompactPseudoUnitaryOffDiagNormSublevel.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.isCompact_pseudoUnitary_offDiag_norm_sublevel : ∀ (n : ℕ) (ε : Fin n → Bool) (C : ℝ), IsCompact {g : UJ ε | ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 ≤ C} := by
  first | exact @GlobalTheory.isCompact_offDiag_sublevel | exact GlobalTheory.isCompact_offDiag_sublevel | (intros; apply GlobalTheory.isCompact_offDiag_sublevel <;> assumption)
