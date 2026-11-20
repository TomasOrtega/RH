import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WorkingFamClassCopiesEqFrozen
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.CountsIrreducibilityConstants
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Pk Formalism.MainNotions.Lnk Formalism.MainNotions.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Fc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Fc.copies_frozen` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FWorkingFamClassCopiesEqFrozen.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.workingFamClass_copies_eq_frozen : (∀ (𝒜 : FamClass) (eps : ℝ) (Fm : FamP eps), (GlobalTheory.Cp.D3 3 𝒜 Fm ↔ W3 𝒜 Fm) ∧ (Formalism.MainNotions.WithTw (Formalism.MainNotions.WithSm (GlobalTheory.Cp.WithChN 𝒜)) Fm ↔ W1 𝒜 Fm)) ∧ ∀ (eps : ℝ) (Fm : FamP eps), DQ.Duty7 Fm → GlobalTheory.Cp.Duty Fm := by
  first | exact @GlobalTheory.Fc.copies_frozen | exact GlobalTheory.Fc.copies_frozen | (intros; apply GlobalTheory.Fc.copies_frozen <;> assumption)
