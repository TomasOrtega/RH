import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThetaFunctionQuasiPeriodic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EvenThetaSecond
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MemOfDenEqZero

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `operator_u_theta`.
-/
theorem opUTh0 : OpUTh0 := operator_u_theta
/- English proof (translation)
The claim follows from `even_theta_line`.
-/
theorem th0Line : ThetaZeroLine := even_theta_line

end Formalism.L2.Th1.F
