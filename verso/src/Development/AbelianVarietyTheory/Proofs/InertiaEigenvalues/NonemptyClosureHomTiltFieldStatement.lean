import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyClosureHomTiltField
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FNonemptyClosureHomTiltField.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.nonempty_closure_hom_tilt_field : ∀ (l : ℕ) [Fact l.Prime], Nonempty (AlgebraicClosure (ZMod l) →+* Per.Fl l) := by
  first | exact @GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | exact GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt | (intros; apply GlobalTheory.Per.nonempty_algClosure_zmod_to_tilt <;> assumption)
