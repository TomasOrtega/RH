import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstIsogeny
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.FormEvenIff

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `quasiPeriodConstIsogeny_thm`.
-/
theorem quasiPeriodConstIsogeny : QuasiPeriodConstIsogeny := quasiPeriodConstIsogeny_thm
/- English proof (translation)
The claim follows from `cm_even_theta`.
-/
theorem cmTheta0 : CmTheta0 := cm_even_theta

end Formalism.L2.Th1.F
