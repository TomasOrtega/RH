import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.SigmaLogDeriv2
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.OperatorUComm
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.SgStar
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.HermHalfRight

namespace Formalism.L2.Th1.F

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem areaPos : AreaPos := areaPos_thm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem etaSplit : EtaSplit := etaSplit_of legendre
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem altEInt : AltEInt := alternating_form_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem altEBasis : AltEBasis := alternating_form_basis
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem semiCharMul : SemiCharMul := semi_character_mul
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUMul : OpUMul := operator_u_mul
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUComm : OpUComm := operator_u_comm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgStarQuasi : SgStarQuasi := sgStarQuasi_of sigmaQuasi etaSplit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgStarFixed : SgStarFixed := sgStarFixed_of sgStarQuasi
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sigmaTaylorLow :
    ∀ L : PeriodPair, iteratedDeriv 2 (wSigma L) 0 = 0 ∧ iteratedDeriv 3 (wSigma L) 0 = 0 :=
  sigmaTaylorLow_of sigmaEntire sigmaSummable
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sgStarBasic : SgStarBasic :=
  sgStarBasic_of sigmaEntire sigmaOdd sigmaZero sigmaSimple sigmaTaylorLow
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th0Const : ThetaZeroConstant := th0Const_of sgStarBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th0Basic : ThetaZeroBasic := th0Basic_of sgStarBasic sgStarQuasi altEInt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th0Class : ThetaZeroClass := th0Class_of sgStarBasic sgStarQuasi
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th0LogDeriv : ThetaZeroLogDerivative := th0LogDeriv_of sigmaLogDeriv etaSplit zetaQuasi zetaOdd

end Formalism.L2.Th1.F
