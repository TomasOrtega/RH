import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsFieldOrExistsSwappedIdempotentOfQuadraticEtale
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsFieldOrExistsSwappedIdempotentOfQuadraticEtale.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.isField_or_exists_swapped_idempotent_of_quadraticEtale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → IsField E ∨ ∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e := by
  first | exact @GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | exact GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA | (intros; apply GlobalTheory.SgAlg.isField_or_exists_idempotent_of_isQA <;> assumption)
