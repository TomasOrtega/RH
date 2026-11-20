import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffDiagBlockNormContInv
import Formalism.RealPlaceAnalysis.SmoothOnGVIff
open MeasureTheory Matrix
open Formalism.REAL (UJ KG toM toMK muK expG inG Jm Kset)
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FOffDiagBlockNormContInv.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.offDiagBlockNorm_mul_invariant : ∀ (n : ℕ) (ε : Fin n → Bool), (Continuous fun g : UJ ε => ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2) ∧ ∀ (k k' : KG ε) (g : UJ ε), ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM ((k : UJ ε) * g * (k' : UJ ε))) z.1.1 z.1.2‖ ^ 2 = ∑ z : {z : Fin n × Fin n // ε z.1 = true ∧ ε z.2 = false}, ‖(toM g) z.1.1 z.1.2‖ ^ 2 := by
  first | exact @GlobalTheory.offDiagBlockNorm_cont_inv | exact GlobalTheory.offDiagBlockNorm_cont_inv | (intros; apply GlobalTheory.offDiagBlockNorm_cont_inv <;> assumption)
