import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.adelicStab_isCompact_isOpen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAdelicLatticeStabiliserIsCompactIsOpen.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.adelicLatticeStabiliser_isCompact_isOpen : ∀ (I : AutInst), IsCompact I.Kset ∧ IsOpen I.Kset ∧ LocallyCompactSpace I.Gf ∧ T2Space I.Gf := by
  first | exact @GlobalTheory.adelicStab_isCompact_isOpen | exact GlobalTheory.adelicStab_isCompact_isOpen | (intros; apply GlobalTheory.adelicStab_isCompact_isOpen <;> assumption)
