import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStandardAdelicAddCharGlobalAdelicChar
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.GlobalFields.TateThesis.AdelicChar
open NumberField Matrix GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FIsStandardAdelicAddCharGlobalAdelicChar.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.isStandardAdelicAddChar_global_adelicChar : ∀ (E : Type) [Field E] [NumberField E], GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) := by
  first | exact @GlobalTheory.StdCharStd.stdPsi_adelicChar | exact GlobalTheory.StdCharStd.stdPsi_adelicChar | (intros; apply GlobalTheory.StdCharStd.stdPsi_adelicChar <;> assumption)
