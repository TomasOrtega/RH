import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvariantsStatementHolds
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.invariants_of_field_of_norms` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FInvariantsStatementHolds.lean&line=338#L338)
-/
theorem _root_.GlobalTheory.T.invariants_statement_holds : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), Formalism.MainNotions.InvariantsGenerators.H0InvariantsTheorem D HW F := by
  first | exact @GlobalTheory.invariants_of_field_of_norms | exact GlobalTheory.invariants_of_field_of_norms | (intros; apply GlobalTheory.invariants_of_field_of_norms <;> assumption)
