import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.QuasiPeriodConstUnique
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.Elliptic
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OnePole
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaOrder
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SigmaAdd
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.PDeriv
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.ThreeTermNumEqTwistedGammaOfSigmaZero

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `elliptic_entire_const`.
-/
theorem ellipticEntire : EllipticEntire := elliptic_entire_const
/- English proof (translation)
The claim follows from `elliptic_no_pole_const`.
-/
theorem ellipticNoPole : EllipticNoPole := elliptic_no_pole_const
/- English proof (translation)
The claim follows from `ellipticOnePole_of ellipticNoPole ellipticEntire zetaQuasi legendre`.
-/
theorem ellipticOnePole : EllipticOnePole :=
  ellipticOnePole_of ellipticNoPole ellipticEntire zetaQuasi legendre
/- English proof (translation)
The claim follows from `sigmaOrder_of sigmaEntire sigmaZero sigmaSimple`.
-/
theorem sigmaOrder : SigmaOrder := sigmaOrder_of sigmaEntire sigmaZero sigmaSimple
/- English proof (translation)
The claim follows from `sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder`.
-/
theorem sigmaAdd : SigmaAdd :=
  sigmaAdd_of ellipticNoPole sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaQuasi sigmaOrder
/- English proof (translation)
The claim follows from `sgStarAdd_of sigmaAdd`.
-/
theorem sgStarAdd : SgStarAdd := sgStarAdd_of sigmaAdd
/- English proof (translation)
The claim follows from `pInjective_of sigmaAdd sigmaZero`.
-/
theorem pInjective : PInjective := pInjective_of sigmaAdd sigmaZero
/- English proof (translation)
The claim follows from `sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple`.
-/
theorem sigmaDouble : SigmaDouble := sigmaDouble_of sigmaAdd sigmaEntire sigmaSimple
/- English proof (translation)
The claim follows from `pDerivZero_of sigmaDouble sigmaZero`.
-/
theorem pDerivZero : PDerivZero := pDerivZero_of sigmaDouble sigmaZero
/- English proof (translation)
The claim follows from `discNeZero_of pDerivZero pInjective`.
-/
theorem discNeZero : DiscNeZero := discNeZero_of pDerivZero pInjective
/- English proof (translation)
The claim follows from `zetaAdd_of sigmaAdd sigmaLogDeriv sigmaZero`.
-/
theorem zetaAdd : ZetaAdd := zetaAdd_of sigmaAdd sigmaLogDeriv sigmaZero
/- English proof (translation)
The claim follows from `sigmaThree_of ellipticOnePole sigmaOrder sigmaQuasi sigmaZero sigmaEntire sigmaOdd sigmaSimple sigmaAdd`.
-/
theorem sigmaThree : SigmaThree :=
  sigmaThree_of ellipticOnePole sigmaOrder sigmaQuasi sigmaZero sigmaEntire sigmaOdd sigmaSimple sigmaAdd
/- English proof (translation)
The claim follows from `sgStarThree_of sigmaThree`.
-/
theorem sgStarThree : SgStarThree := sgStarThree_of sigmaThree
/- English proof (translation)
The claim follows from `thetaLine_of ellipticOnePole sgStarQuasi sgStarBasic`.
-/
theorem thetaLine : ThetaLine := thetaLine_of ellipticOnePole sgStarQuasi sgStarBasic

end Formalism.L2.Th1.F
