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
A detailed English derivation is pending.
-/
theorem nonsingNorm : NonsingNorm := nonsingular_norm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitKap : UnitKap := UnitKap_of nonsingNorm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitPsi2 : UnitPsi2 := UnitPsi2_of nonsingNorm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitDiff : UnitDiff := UnitDiff_of nonsingNorm
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intRules : IntRules := integrality_rules
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitAtRules : UnitAtRules := unit_at_rules
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rootInt : RootInt := root_integral_alt
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gaussMul : GaussMul := gauss_multiplicative
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xTShape : XTShape := XTShape_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem facShape : FacShape := FacShape_of intRules unitAtRules unitKap unitPsi2 unitDiff xTShape
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transPower : TransPower := translate_power
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem parSumTwo : ParSumTwo := parallelogram_sum_two
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transUnit : TransUnit := TransUnit_of intRules unitAtRules rootInt facShape transPower
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transGauss : TransGauss := TransGauss_of intRules unitAtRules transUnit

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem prodInt : ProdInt := product_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem substExpInt : SubstExpInt := subst_exp_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem congIffSimeq : CongIffSimeq := congruence_iff_simeq
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sumEBridge : SumEBridge := sum_series_analytic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mapCob : MapCob := map_coboundary
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intHyp : IntHyp :=
  IntHyp_of prodInt substExpInt congIffSimeq Formalism.L2.Th1.C.hyperbolicSum Formalism.L2.Th1.C.ptClosure

end Formalism.L2.Th1.E
