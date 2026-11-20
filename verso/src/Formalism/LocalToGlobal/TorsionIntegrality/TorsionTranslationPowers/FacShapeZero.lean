import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.NonsingularNorm
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Series
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInvTDen
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledXEqOffOrigin
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledXOffOrigin
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ConstantCoeffInVarEqZero
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.PhNormFromDatum
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.BiextensionHypothesesOfLevelOne

namespace Formalism.L2.Th1.E

/- English proof (translation)
The claim follows from `nonsingular_norm`.
-/
theorem nonsingNorm : NonsingNorm := nonsingular_norm
/- English proof (translation)
The claim follows from `UnitKap_of nonsingNorm`.
-/
theorem unitKap : UnitKap := UnitKap_of nonsingNorm
/- English proof (translation)
The claim follows from `UnitPsi2_of nonsingNorm`.
-/
theorem unitPsi2 : UnitPsi2 := UnitPsi2_of nonsingNorm
/- English proof (translation)
The claim follows from `UnitDiff_of nonsingNorm`.
-/
theorem unitDiff : UnitDiff := UnitDiff_of nonsingNorm
/- English proof (translation)
The claim follows from `integrality_rules`.
-/
theorem intRules : IntRules := integrality_rules
/- English proof (translation)
The claim follows from `unit_at_rules`.
-/
theorem unitAtRules : UnitAtRules := unit_at_rules
/- English proof (translation)
The claim follows from `root_integral_alt`.
-/
theorem rootInt : RootInt := root_integral_alt
/- English proof (translation)
The claim follows from `gauss_multiplicative`.
-/
theorem gaussMul : GaussMul := gauss_multiplicative
/- English proof (translation)
The claim follows from `XTShape_holds`.
-/
theorem xTShape : XTShape := XTShape_holds
/- English proof (translation)
The claim follows from `FacShape_of intRules unitAtRules unitKap unitPsi2 unitDiff xTShape`.
-/
theorem facShape : FacShape := FacShape_of intRules unitAtRules unitKap unitPsi2 unitDiff xTShape
/- English proof (translation)
The claim follows from `translate_power`.
-/
theorem transPower : TransPower := translate_power
/- English proof (translation)
The claim follows from `parallelogram_sum_two`.
-/
theorem parSumTwo : ParSumTwo := parallelogram_sum_two
/- English proof (translation)
The claim follows from `TransUnit_of intRules unitAtRules rootInt facShape transPower`.
-/
theorem transUnit : TransUnit := TransUnit_of intRules unitAtRules rootInt facShape transPower
/- English proof (translation)
The claim follows from `TransGauss_of intRules unitAtRules transUnit`.
-/
theorem transGauss : TransGauss := TransGauss_of intRules unitAtRules transUnit

/- English proof (translation)
The claim follows from `product_integral`.
-/
theorem prodInt : ProdInt := product_integral
/- English proof (translation)
The claim follows from `subst_exp_integral`.
-/
theorem substExpInt : SubstExpInt := subst_exp_integral
/- English proof (translation)
The claim follows from `congruence_iff_simeq`.
-/
theorem congIffSimeq : CongIffSimeq := congruence_iff_simeq
/- English proof (translation)
The claim follows from `sum_series_analytic`.
-/
theorem sumEBridge : SumEBridge := sum_series_analytic
/- English proof (translation)
The claim follows from `map_coboundary`.
-/
theorem mapCob : MapCob := map_coboundary
/- English proof (translation)
The claim follows from `IntHyp_of prodInt substExpInt congIffSimeq Formalism.L2.Th1.C.hyperbolicSum Formalism.L2.Th1.C.ptClosure`.
-/
theorem intHyp : IntHyp :=
  IntHyp_of prodInt substExpInt congIffSimeq Formalism.L2.Th1.C.hyperbolicSum Formalism.L2.Th1.C.ptClosure

end Formalism.L2.Th1.E
