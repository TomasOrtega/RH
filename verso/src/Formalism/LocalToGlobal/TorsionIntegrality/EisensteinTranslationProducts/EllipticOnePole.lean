import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Elliptic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaOrder
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaAdd
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.PDeriv
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThreeTermNumEqTwistedGammaOfSigmaZero

namespace Formalism.L2.Th1.F

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ellipticEntire : EllipticEntire := elliptic_entire_const
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ellipticNoPole : EllipticNoPole := elliptic_no_pole_const
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ellipticOnePole : EllipticOnePole :=
  ellipticOnePole_of ellipticNoPole ellipticEntire zetaQuasi legendre
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaOrder : SigmaOrder := sigmaOrder_of sigmaEntire sigmaZero sigmaSimple
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaAdd : SigmaAdd :=
  sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgStarAdd : SgStarAdd := sgStarAdd_of sigmaAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pInjective : PInjective := pInjective_of sigmaAdd sigmaZero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaDouble : SigmaDouble := sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pDerivZero : PDerivZero := pDerivZero_of sigmaDouble sigmaZero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem discNeZero : DiscNeZero := discNeZero_of pDerivZero pInjective
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem zetaAdd : ZetaAdd := zetaAdd_of sigmaAdd sigmaLogDeriv sigmaZero
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaThree : SigmaThree :=
  sigmaThree_of ellipticOnePole sigmaOrder sigmaQuasi sigmaZero sigmaEntire sigmaOdd sigmaSimple sigmaAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgStarThree : SgStarThree := sgStarThree_of sigmaThree
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem thetaLine : ThetaLine := thetaLine_of ellipticOnePole sgStarQuasi sgStarBasic

end Formalism.L2.Th1.F
