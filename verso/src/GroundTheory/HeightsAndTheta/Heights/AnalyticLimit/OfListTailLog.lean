import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Assembly
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListProductMass
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLog
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PListTailLogSmooth
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PProductBounds
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStep
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplace
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassError
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PWeightCocycle
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPolynomialInWeights
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Imports
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PPropertyF
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GreenMassStep.full : GreenMassStep.Statement := GreenMassStep.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GreenMassReplace.full : GreenMassReplace.Statement := GreenMassReplace.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GreenMassError.full : GreenMassError.Statement := GreenMassError.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UniformIntegrability.full : UniformIntegrability.Statement :=
  UniformIntegrability.of_greenMass GreenMassStep.full GreenMassReplace.full GreenMassError.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem WeightCocycle.full : WeightCocycle.Statement := WeightCocycle.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PolynomialInWeights.full : PolynomialInWeights.Statement := PolynomialInWeights.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Convergence.full : Convergence.Statement := Convergence.proof WeightCocycle.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem CoefficientLimit.full : CoefficientLimit.Statement :=
  CoefficientLimit.proof WeightCocycle.full PolynomialInWeights.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ArgumentConvergenceC2.full : ArgumentConvergenceC2.Statement := ArgumentConvergenceC2.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PropertyF.full : PropertyF.Statement := PropertyF.proof GluedLocal.full ArgumentConvergenceC2.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ListProductMass.full : ListProductMass.Statement := ListProductMass.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ListTailLog.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement :=
  ListTailLog.proof hE hM hC hS

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TailBound.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : TailBound.Statement :=
  TailBound.of_listTailLog (ListTailLog.of_lemmaE hE hM hC hS)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ListTailLogSmooth.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLogSmooth.Statement :=
  ListTailLogSmooth.proof (ListTailLog.of_lemmaE hE hM hC hS)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProductBounds.of_listTailLog (h : ListTailLog.Statement) : ProductBounds.Statement :=
  ProductBounds.proof ListProductMass.full (ListTailLogSmooth.proof h)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ProductBounds.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ProductBounds.Statement :=
  ProductBounds.of_listTailLog (ListTailLog.of_lemmaE hE hM hC hS)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SystemIndependence.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : SystemIndependence.Statement :=
  SystemIndependence.of_productBounds (ProductBounds.of_lemmaE hE hM hC hS)

end GroundTheory.Heights₂.Heights.AnalyticLimit
