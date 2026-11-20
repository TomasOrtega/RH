import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.HcMultDSOfAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.HasDerivAtDS
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.GenApplyEqZero
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.AdmissibleCasimirScalars.SmoothGeneratorAverages.ImInnerSelf

set_option autoImplicit false

namespace Formalism.L2.SG.Pf.admitted

/- English proof (translation)
The claim follows from `casScalar_of c1 c2 c3`.
-/
theorem casScalar : CasScalarStatement := casScalar_of c1 c2 c3

end Formalism.L2.SG.Pf.admitted
