import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.FacShapeZero
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.GeneralIntegrality
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.Taylor0ConstMul
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.AnaSys
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.CmIntegralityOfTorsionPoints
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.OpUTh0RootOf
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ExistsFinitePartOneIdeleSplitCongruenceQuotient
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.NonsingularJetNorms.ScaledTorsionPointNonsingular

namespace Formalism.L2.Th1.E

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem fourthPower : FourthPower := fourth_power
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem generalIntOf : GeneralIntOf := general_integrality
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem torsionIntegral : TorsionIntegral := torsion_integral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptOfZero : PtOfZero := PtOfZero_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem wpBridge : WpBridge := AnaSys.wpBridge
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem transWpBridge : TransWpBridge := AnaSys.transWpBridge
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem analyticSys : AnalyticSys := AnalyticSys_of transWpBridge
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cm4OfHalves : CMTorsionValuesOfIntegralAndUnramified := cm_integrality_of_halves
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem opUTh0Root : OpUTh0Root := OpUTh0Root_of

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptOfInt_of_add (hA : PtOfAdd) : PtOfInt := PtOfInt_of hA ptOfZero torsionIntegral
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelPtInt_of_add (hA : PtOfAdd) : KernelPtInt := KernelPtInt_of (ptOfInt_of_add hA)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cm4Int_of_add (hA : PtOfAdd) : CMIntegrality := cm_integrality_of_torsion_points (ptOfInt_of_add hA)
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem analyticTrans_of_add (hA : PtOfAdd) : AnalyticTrans :=
  AnalyticTrans_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th0Analytic_of_add (hA : PtOfAdd) : ThetaZeroAnalytic :=
  Th0Analytic_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit transGauss opUTh0Root

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptOfAdd : PtOfAdd := PtOfAdd_of
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptOfInt : PtOfInt := ptOfInt_of_add ptOfAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kernelPtInt : KernelPtInt := kernelPtInt_of_add ptOfAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cm4Int : CMIntegrality := cm4Int_of_add ptOfAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem analyticTrans : AnalyticTrans := analyticTrans_of_add ptOfAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem th0Analytic : ThetaZeroAnalytic := th0Analytic_of_add ptOfAdd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cm4Pt : ScaledTorsionPointNonsingular := scaled_torsion_point_of_add ptOfAdd

end Formalism.L2.Th1.E
