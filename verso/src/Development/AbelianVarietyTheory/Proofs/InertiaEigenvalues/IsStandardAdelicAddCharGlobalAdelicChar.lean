import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import GroundTheory.GlobalFields.TateThesis.AdelicChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPsiLocNeOne

open NumberField Matrix GlobalTheory.CuspRep

namespace GlobalTheory.StdCharStd

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem stdPsi_adelicChar : ∀ (E : Type) [Field E] [NumberField E],
    GlobalTheory.CuspGeneric.StdPsi (Circle.coeHom.compAddChar (GroundTheory.Global.adelicChar E)) :=
  fun E _ _ => GlobalTheory.StdCharConductor.stdPsi_psi E

end GlobalTheory.StdCharStd
