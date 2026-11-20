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
A detailed English derivation is pending.
-/
theorem RegularizedMaxConvergenceC2.full : RegularizedMaxConvergenceC2.Statement := RegularizedMaxConvergenceC2.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GluedLocal.full : GluedLocal.Statement := GluedLocal.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConvergenceRate.full : ConvergenceRate.Statement := ConvergenceRate.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ConvergenceSigned.full : ConvergenceSigned.Statement := ConvergenceSigned.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EnergyStep.full : EnergyStep.Statement := EnergyStep.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem EnergySum.full : EnergySum.Statement := EnergySum.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem RegularisedMonotone.full : RegularisedMonotone.Statement := RegularisedMonotone.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem KaehlerBound.full : KaehlerBound.Statement := KaehlerBound.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem BoundingKaehler.full : BoundingKaehler.Statement := BoundingKaehler.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LinearWeights.full : LinearWeights.Statement := LinearWeights.proof KaehlerBound.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem C2ConvergencePullback.full : C2ConvergencePullback.Statement := C2ConvergencePullback.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SystemPullback.full : SystemPullback.Statement := SystemPullback.proof C2ConvergencePullback.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem DivisorNull.full : DivisorNull.Statement := DivisorNull.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem GreenMassZero.full : GreenMassZero.Statement := GreenMassZero.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem Telescoping.full : Telescoping.Statement := Telescoping.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TelescopingFamily.full : TelescopingFamily.Statement := TelescopingFamily.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem TailBound.of_listTailLog (h : ListTailLog.Statement) : TailBound.Statement :=
  TailBound.proof h BoundingKaehler.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SystemIndependence.of_productBounds (h : ProductBounds.Statement) :
    SystemIndependence.Statement :=
  SystemIndependence.proof DivisorNull.full h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem UniformIntegrability.of_greenMass (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement :=
  UniformIntegrability.proof GreenMassZero.full h₁ h₂ h₃

end GroundTheory.Heights₂.Heights.AnalyticLimit
