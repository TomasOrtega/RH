import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OperatorUComm
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SgStar
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HermHalfRight

namespace Formalism.L2.Th1.F

/- English proof (translation)
The claim follows from `areaPos_thm`.
-/
theorem areaPos : AreaPos := areaPos_thm
/- English proof (translation)
The claim follows from `etaSplit_of legendre`.
-/
theorem etaSplit : EtaSplit := etaSplit_of legendre
/- English proof (translation)
The claim follows from `alternating_form_integral`.
-/
theorem altEInt : AltEInt := alternating_form_integral
/- English proof (translation)
The claim follows from `alternating_form_basis`.
-/
theorem altEBasis : AltEBasis := alternating_form_basis
/- English proof (translation)
The claim follows from `semi_character_mul`.
-/
theorem semiCharMul : SemiCharMul := semi_character_mul
/- English proof (translation)
The claim follows from `operator_u_mul`.
-/
theorem opUMul : OpUMul := operator_u_mul
/- English proof (translation)
The claim follows from `operator_u_comm`.
-/
theorem opUComm : OpUComm := operator_u_comm
/- English proof (translation)
The claim follows from `sgStarQuasi_of sigmaQuasi etaSplit`.
-/
theorem sgStarQuasi : SgStarQuasi := sgStarQuasi_of sigmaQuasi etaSplit
/- English proof (translation)
The claim follows from `sgStarFixed_of sgStarQuasi`.
-/
theorem sgStarFixed : SgStarFixed := sgStarFixed_of sgStarQuasi
/- English proof (translation)
The claim follows from `sigmaTaylorLow_of sigmaEntire sigmaSummable`.
-/
theorem sigmaTaylorLow :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 :=
  sigmaTaylorLow_of sigmaEntire sigmaSummable
/- English proof (translation)
The claim follows from `sgStarBasic_of sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaTaylorLow`.
-/
theorem sgStarBasic : SgStarBasic :=
  sgStarBasic_of sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaTaylorLow
/- English proof (translation)
The claim follows from `th0Const_of sgStarBasic`.
-/
theorem th0Const : ThetaZeroConstant := th0Const_of sgStarBasic
/- English proof (translation)
The claim follows from `th0Basic_of sgStarBasic sgStarQuasi altEInt`.
-/
theorem th0Basic : ThetaZeroBasic := th0Basic_of sgStarBasic sgStarQuasi altEInt
/- English proof (translation)
The claim follows from `th0Class_of sgStarBasic sgStarQuasi`.
-/
theorem th0Class : ThetaZeroClass := th0Class_of sgStarBasic sgStarQuasi
/- English proof (translation)
The claim follows from `th0LogDeriv_of sigmaLogDeriv etaSplit zetaQuasi zetaOdd`.
-/
theorem th0LogDeriv : ThetaZeroLogDerivative := th0LogDeriv_of sigmaLogDeriv etaSplit zetaQuasi zetaOdd

end Formalism.L2.Th1.F
