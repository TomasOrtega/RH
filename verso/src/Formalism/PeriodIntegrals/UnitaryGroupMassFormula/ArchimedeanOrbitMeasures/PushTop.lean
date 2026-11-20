import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DetNZHolds
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SdTestC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.AprimeInfOfLeaves

noncomputable section

namespace PI.AprimeInfW

/- English proof (translation)
The claim follows from `pushInf_of invPush_holds invFib_holds (lfPush_of detNZ_holds hL) lfFib_holds hU hC`.
-/
theorem pushInf_of_pushLFin_of_orbUniq_of_constTest (hL : PushLFin) (hU : OrbUniq) (hC : ConstTest) : PushInf :=
  pushInf_of invPush_holds invFib_holds (lfPush_of detNZ_holds hL) lfFib_holds hU hC

/- English proof (translation)
The claim follows from `aprimeInf_iff.2 (aprimeInfS_of (ainfValue_of hE (pushInf_of_pushLFin_of_orbUniq_of_constTest hL hU hC) hW hH) hG)`.
-/
theorem aprimeInf_of_pushSteps (hE : ExInf) (hL : PushLFin) (hU : OrbUniq) (hC : ConstTest)
    (hW : WeilInf) (hH : HtotInf) (hG : GinfTest) : Formalism.L2.SG.Pf.NcReal.AprimeInf :=
  aprimeInf_iff.2 (aprimeInfS_of (ainfValue_of hE (pushInf_of_pushLFin_of_orbUniq_of_constTest hL hU hC) hW hH) hG)

end PI.AprimeInfW
