import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiberConjugationStripInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtMapApply
open Matrix MeasureTheory Set GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm
open scoped ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TorsionForm.strN_frame_conj` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiberConjugationStripInvariant.lean&line=343#L343)
-/
theorem _root_.GlobalTheory.T.fiber_conjugation_strip_invariant : ∀ {n g : ℕ} (a a' : Matrix (Fin g) (Fin g) ℂ), a' * a = 1 → ∀ K : Ext (n + n + g) →L[ℂ] Ext (n + n + g), strN (m := n + n) (extMap (fibMat n a) ∘L K ∘L extMap (fibMat n a')) = strN (m := n + n) K := by
  first | exact @GlobalTheory.TorsionForm.strN_frame_conj | exact GlobalTheory.TorsionForm.strN_frame_conj | (intros; apply GlobalTheory.TorsionForm.strN_frame_conj <;> assumption)
