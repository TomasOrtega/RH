import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameDetIsUnitOfIsotropic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullFrameRight
open GlobalTheory.WholeFlag GlobalTheory.WholeFlag.Glue
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFullFrameDetIsUnitOfIsotropic.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.full_frame_det_isUnit_of_isotropic : ∀ {R : Type} [CommRing R] [IsLocalRing R] {g : ℕ} (U : Matrix (Fin (g + g)) (Fin g) R) (J : Matrix (Fin (g + g)) (Fin (g + g)) R) (τ : Fin g → Fin (g + g)), IsUnit J.det → IsUnit (rowSel τ * U : Matrix (Fin g) (Fin g) R).det → (∀ i k, (U.transpose * J * U) i k ∈ IsLocalRing.maximalIdeal R) → IsUnit (fullFrame U J (leftInv U τ)).det := by
  first | exact @GlobalTheory.WholeFlag.Glue.isUnit_det_fullFrame_local | exact GlobalTheory.WholeFlag.Glue.isUnit_det_fullFrame_local | (intros; apply GlobalTheory.WholeFlag.Glue.isUnit_det_fullFrame_local <;> assumption)
