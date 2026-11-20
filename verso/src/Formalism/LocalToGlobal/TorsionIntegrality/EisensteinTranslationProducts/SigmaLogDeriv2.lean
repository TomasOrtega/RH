import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.AnalyticIdentityTheoremsZetaFacts
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaConv
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaBasic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaLog
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ZetaQuasi
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaQuasi
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.EtaEis
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Legendre

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `zeta_summable`.
-/
theorem zetaSummable : ZetaSummable := zeta_summable
/- English proof (translation)
The claim follows from `zeta_has_deriv`.
-/
theorem zetaHasDeriv : ZetaHasDeriv := zeta_has_deriv
/- English proof (translation)
The claim follows from `zeta_odd`.
-/
theorem zetaOdd : ZetaOdd := zeta_odd
/- English proof (translation)
The claim follows from `zetaQuasi_of zetaHasDeriv zetaOdd`.
-/
theorem zetaQuasi : ZetaQuasi := zetaQuasi_of zetaHasDeriv zetaOdd
/- English proof (translation)
The claim follows from `sigma_summable`.
-/
theorem sigmaSummable : SigmaSummable := sigma_summable
/- English proof (translation)
The claim follows from `sigma_product_locally_uniform`.
-/
theorem sigmaProdLU : SigmaProdLU := sigma_product_locally_uniform
/- English proof (translation)
The claim follows from `sigmaEntire_of sigmaProdLU`.
-/
theorem sigmaEntire : SigmaEntire := sigmaEntire_of sigmaProdLU
/- English proof (translation)
The claim follows from `sigma_odd`.
-/
theorem sigmaOdd : SigmaOdd := sigma_odd
/- English proof (translation)
The claim follows from `sigmaZero_of sigmaSummable`.
-/
theorem sigmaZero : SigmaZero := sigmaZero_of sigmaSummable
/- English proof (translation)
The claim follows from `sigmaLogDeriv_of sigmaProdLU sigmaSummable zetaSummable`.
-/
theorem sigmaLogDeriv : SigmaLogDeriv := sigmaLogDeriv_of sigmaProdLU sigmaSummable zetaSummable
/- English proof (translation)
The claim follows from `sigmaQuasi_of zetaQuasi sigmaLogDeriv sigmaEntire sigmaOdd sigmaZero`.
-/
theorem sigmaQuasi : SigmaQuasi := sigmaQuasi_of zetaQuasi sigmaLogDeriv sigmaEntire sigmaOdd sigmaZero
/- English proof (translation)
The claim follows from `sigmaSimple_of sigmaQuasi sigmaEntire (sigmaDerivZero_of sigmaProdLU)`.
-/
theorem sigmaSimple : SigmaSimple := sigmaSimple_of sigmaQuasi sigmaEntire (sigmaDerivZero_of sigmaProdLU)
/- English proof (translation)
The claim follows from `etaEisenstein_of zetaSummable zetaOdd`.
-/
theorem etaEisenstein : EtaEisenstein := etaEisenstein_of zetaSummable zetaOdd
/- English proof (translation)
The claim follows from `legendre_of etaEisenstein`.
-/
theorem legendre : Legendre := legendre_of etaEisenstein

end Formalism.L2.Th1.F
