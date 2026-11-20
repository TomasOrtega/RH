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
The claim follows from `fourth_power`.
-/
theorem fourthPower : FourthPower := fourth_power
/- English proof (translation)
The claim follows from `general_integrality`.
-/
theorem generalIntOf : GeneralIntOf := general_integrality
/- English proof (translation)
The claim follows from `torsion_integral`.
-/
theorem torsionIntegral : TorsionIntegral := torsion_integral
/- English proof (translation)
The claim follows from `PtOfZero_of`.
-/
theorem ptOfZero : PtOfZero := PtOfZero_of
/- English proof (translation)
The claim follows from `AnaSys.wpBridge`.
-/
theorem wpBridge : WpBridge := AnaSys.wpBridge
/- English proof (translation)
The claim follows from `AnaSys.transWpBridge`.
-/
theorem transWpBridge : TransWpBridge := AnaSys.transWpBridge
/- English proof (translation)
The claim follows from `AnalyticSys_of transWpBridge`.
-/
theorem analyticSys : AnalyticSys := AnalyticSys_of transWpBridge
/- English proof (translation)
The claim follows from `cm_integrality_of_halves`.
-/
theorem cm4OfHalves : CMTorsionValuesOfIntegralAndUnramified := cm_integrality_of_halves
/- English proof (translation)
The claim follows from `OpUTh0Root_of`.
-/
theorem opUTh0Root : OpUTh0Root := OpUTh0Root_of

/- English proof (translation)
The claim follows from `PtOfInt_of hA ptOfZero torsionIntegral`.
-/
theorem ptOfInt_of_add (hA : PtOfAdd) : PtOfInt := PtOfInt_of hA ptOfZero torsionIntegral
/- English proof (translation)
The claim follows from `KernelPtInt_of (ptOfInt_of_add hA)`.
-/
theorem kernelPtInt_of_add (hA : PtOfAdd) : KernelPtInt := KernelPtInt_of (ptOfInt_of_add hA)
/- English proof (translation)
The claim follows from `cm_integrality_of_torsion_points (ptOfInt_of_add hA)`.
-/
theorem cm4Int_of_add (hA : PtOfAdd) : CMIntegrality := cm_integrality_of_torsion_points (ptOfInt_of_add hA)
/- English proof (translation)
The claim follows from `AnalyticTrans_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit`.
-/
theorem analyticTrans_of_add (hA : PtOfAdd) : AnalyticTrans :=
  AnalyticTrans_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit
/- English proof (translation)
The claim follows from `Th0Analytic_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit transGauss opUTh0Root`.
-/
theorem th0Analytic_of_add (hA : PtOfAdd) : ThetaZeroAnalytic :=
  Th0Analytic_of analyticSys hA ptOfZero (ptOfInt_of_add hA) transUnit transGauss opUTh0Root

/- English proof (translation)
The claim follows from `PtOfAdd_of`.
-/
theorem ptOfAdd : PtOfAdd := PtOfAdd_of
/- English proof (translation)
The claim follows from `ptOfInt_of_add ptOfAdd`.
-/
theorem ptOfInt : PtOfInt := ptOfInt_of_add ptOfAdd
/- English proof (translation)
The claim follows from `kernelPtInt_of_add ptOfAdd`.
-/
theorem kernelPtInt : KernelPtInt := kernelPtInt_of_add ptOfAdd
/- English proof (translation)
The claim follows from `cm4Int_of_add ptOfAdd`.
-/
theorem cm4Int : CMIntegrality := cm4Int_of_add ptOfAdd
/- English proof (translation)
The claim follows from `analyticTrans_of_add ptOfAdd`.
-/
theorem analyticTrans : AnalyticTrans := analyticTrans_of_add ptOfAdd
/- English proof (translation)
The claim follows from `th0Analytic_of_add ptOfAdd`.
-/
theorem th0Analytic : ThetaZeroAnalytic := th0Analytic_of_add ptOfAdd
/- English proof (translation)
The claim follows from `scaled_torsion_point_of_add ptOfAdd`.
-/
theorem cm4Pt : ScaledTorsionPointNonsingular := scaled_torsion_point_of_add ptOfAdd

end Formalism.L2.Th1.E
