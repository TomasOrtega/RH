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
A detailed English derivation is pending.
-/
theorem zetaSummable : ZetaSummable := zeta_summable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zetaHasDeriv : ZetaHasDeriv := zeta_has_deriv
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zetaOdd : ZetaOdd := zeta_odd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zetaQuasi : ZetaQuasi := zetaQuasi_of zetaHasDeriv zetaOdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaSummable : SigmaSummable := sigma_summable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaProdLU : SigmaProdLU := sigma_product_locally_uniform
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaEntire : SigmaEntire := sigmaEntire_of sigmaProdLU
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaOdd : SigmaOdd := sigma_odd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaZero : SigmaZero := sigmaZero_of sigmaSummable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaLogDeriv : SigmaLogDeriv := sigmaLogDeriv_of sigmaProdLU sigmaSummable zetaSummable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaQuasi : SigmaQuasi := sigmaQuasi_of zetaQuasi sigmaLogDeriv sigmaEntire sigmaOdd sigmaZero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaSimple : SigmaSimple := sigmaSimple_of sigmaQuasi sigmaEntire (sigmaDerivZero_of sigmaProdLU)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etaEisenstein : EtaEisenstein := etaEisenstein_of zetaSummable zetaOdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem legendre : Legendre := legendre_of etaEisenstein

end Formalism.L2.Th1.F
