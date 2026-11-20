import Mathlib
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Convergence
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.ConvergenceRate
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergyStep
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.EnergySum
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Monotone
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PBoundingKaehler
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TendstoLocallyUniformlyOnOfNhds
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PDivisorNull
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGluedLocal
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassZero
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PKaehlerBound
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.LinearWeights
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Pullback
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.TailBound
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Telescoping
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UniformIntegrability
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.AgreementOnBase
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPushDown
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.LowerBoundFree

/- English proof (translation)
The claim follows from `RegularizedMaxConvergenceC2.proof`.
-/
theorem RegularizedMaxConvergenceC2.full : RegularizedMaxConvergenceC2.Statement := RegularizedMaxConvergenceC2.proof

/- English proof (translation)
The claim follows from `GluedLocal.proof`.
-/
theorem GluedLocal.full : GluedLocal.Statement := GluedLocal.proof

/- English proof (translation)
The claim follows from `ConvergenceRate.proof`.
-/
theorem ConvergenceRate.full : ConvergenceRate.Statement := ConvergenceRate.proof

/- English proof (translation)
The claim follows from `ConvergenceSigned.proof`.
-/
theorem ConvergenceSigned.full : ConvergenceSigned.Statement := ConvergenceSigned.proof

/- English proof (translation)
The claim follows from `EnergyStep.proof`.
-/
theorem EnergyStep.full : EnergyStep.Statement := EnergyStep.proof

/- English proof (translation)
The claim follows from `EnergySum.proof`.
-/
theorem EnergySum.full : EnergySum.Statement := EnergySum.proof

/- English proof (translation)
The claim follows from `RegularisedMonotone.proof`.
-/
theorem RegularisedMonotone.full : RegularisedMonotone.Statement := RegularisedMonotone.proof

/- English proof (translation)
The claim follows from `KaehlerBound.proof`.
-/
theorem KaehlerBound.full : KaehlerBound.Statement := KaehlerBound.proof

/- English proof (translation)
The claim follows from `BoundingKaehler.proof`.
-/
theorem BoundingKaehler.full : BoundingKaehler.Statement := BoundingKaehler.proof

/- English proof (translation)
The claim follows from `LinearWeights.proof KaehlerBound.full`.
-/
theorem LinearWeights.full : LinearWeights.Statement := LinearWeights.proof KaehlerBound.full

/- English proof (translation)
The claim follows from `C2ConvergencePullback.proof`.
-/
theorem C2ConvergencePullback.full : C2ConvergencePullback.Statement := C2ConvergencePullback.proof

/- English proof (translation)
The claim follows from `SystemPullback.proof C2ConvergencePullback.full`.
-/
theorem SystemPullback.full : SystemPullback.Statement := SystemPullback.proof C2ConvergencePullback.full

/- English proof (translation)
The claim follows from `DivisorNull.proof`.
-/
theorem DivisorNull.full : DivisorNull.Statement := DivisorNull.proof

/- English proof (translation)
The claim follows from `GreenMassZero.proof`.
-/
theorem GreenMassZero.full : GreenMassZero.Statement := GreenMassZero.proof

/- English proof (translation)
The claim follows from `Telescoping.proof`.
-/
theorem Telescoping.full : Telescoping.Statement := Telescoping.proof

/- English proof (translation)
The claim follows from `TelescopingFamily.proof`.
-/
theorem TelescopingFamily.full : TelescopingFamily.Statement := TelescopingFamily.proof

/- English proof (translation)
The claim follows from `TailBound.proof h BoundingKaehler.full`.
-/
theorem TailBound.of_listTailLog (h : ListTailLog.Statement) : TailBound.Statement :=
  TailBound.proof h BoundingKaehler.full

/- English proof (translation)
The claim follows from `SystemIndependence.proof DivisorNull.full h`.
-/
theorem SystemIndependence.of_productBounds (h : ProductBounds.Statement) :
    SystemIndependence.Statement :=
  SystemIndependence.proof DivisorNull.full h

/- English proof (translation)
The claim follows from `UniformIntegrability.proof GreenMassZero.full h₁ h₂ h₃`.
-/
theorem UniformIntegrability.of_greenMass (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement :=
  UniformIntegrability.proof GreenMassZero.full h₁ h₂ h₃

end GroundTheory.Heights₂.Heights.AnalyticLimit
