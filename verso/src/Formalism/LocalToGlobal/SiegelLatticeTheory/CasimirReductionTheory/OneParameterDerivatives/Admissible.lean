import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.GgExistsAddCharNeOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.KFinSmooth

set_option autoImplicit false

namespace Formalism.L2.SG.Pf

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.admitted.hcMultDS`.
-/
theorem harishChandra_multiplicity : Formalism.MainNotions.BridgeCPX.HCMultDS := Formalism.L2.SG.Pf.admitted.hcMultDS

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.admitted.hcAdmDS`.
-/
theorem harishChandra_admissible : Formalism.MainNotions.BridgeCPX.HCAdmDS := Formalism.L2.SG.Pf.admitted.hcAdmDS

/- English proof (translation)
Unfold `Formalism.L2.SG.LitS.KFinSmooth`. Conclude with `Formalism.L2.SG.Pf.admitted.kFinSmooth'`.
-/
theorem k_finite_smooth : Formalism.L2.SG.LitS.KFinSmooth := by
  unfold Formalism.L2.SG.LitS.KFinSmooth
  exact Formalism.L2.SG.Pf.admitted.kFinSmooth'

/- English proof (translation)
The claim follows from `Formalism.L2.SG.Pf.admitted.kFinSmooth`.
-/
theorem k_finite_smooth_bessel : Formalism.MainNotions.LowestKTypeMultiplicity.KFinSmooth := Formalism.L2.SG.Pf.admitted.kFinSmooth

end Formalism.L2.SG.Pf
