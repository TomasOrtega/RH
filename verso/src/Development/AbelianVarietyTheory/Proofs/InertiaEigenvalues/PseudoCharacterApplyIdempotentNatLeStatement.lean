import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PseudoCharacterApplyIdempotentNatLe
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
open Formalism.MainNotions.N GlobalTheory.PsChar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PsChar.isPsChar_idempotent` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPseudoCharacterApplyIdempotentNatLe.lean&line=48#L48)
-/
theorem _root_.GlobalTheory.T.pseudoCharacter_apply_idempotent_nat_le : ∀ (k R : Type) [Field k] [CharZero k] [Ring R] [Algebra k R] (d : ℕ) (T : R →ₗ[k] k), IsPsChar d (fun x => T x) → ∀ e : R, IsIdempotentElem e → (∃ m : ℕ, m ≤ d ∧ T e = m) ∧ (T e = 0 → ∀ y : R, T (e * y) = 0) := by
  first | exact @GlobalTheory.PsChar.isPsChar_idempotent | exact GlobalTheory.PsChar.isPsChar_idempotent | (intros; apply GlobalTheory.PsChar.isPsChar_idempotent <;> assumption)
