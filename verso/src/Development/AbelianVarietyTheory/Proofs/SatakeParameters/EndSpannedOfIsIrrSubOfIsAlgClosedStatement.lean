import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EndSpannedOfIsIrrSubOfIsAlgClosed
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MapMulVecMemOfMemSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanRepMatrixEqTopOfAbsIrreducible
open Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.SplitField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FEndSpannedOfIsIrrSubOfIsAlgClosed.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.endSpanned_of_isIrrSub_of_isAlgClosed' : ∀ {Γ E : Type} [Group Γ] [Field E] [IsAlgClosed E] {a : ℕ} (σ : Γ →* GL (Fin a) E) (U : Submodule E (Fin a → E)), IsIrrSub σ U → EndSpanned σ U := by
  first | exact @GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed | exact GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed | (intros; apply GlobalTheory.SplitField.endSpanned_of_isIrrSub_of_isAlgClosed <;> assumption)
