import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormLength
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PVertTermEq
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IsChowFormCMul
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveUnit
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PGaussEq
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParAlgIndep
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBLinInj
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormEval
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowSecDegree
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormIdentity
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.POrdEq
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChartTorsion
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowFormHomog
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormFormGeneric
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PChowNormForm
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PIncidenceNull
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PLengthDecomp
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PNormFormLocalization
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParDVRIsDVR
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PParFracIsFractionRing
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PPrimitiveScale
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecAlgField
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBFinite
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecBGeneric
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSecLinNZD
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecMax
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecResidue
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

/- English proof (translation)
The claim follows from `NormLength.proof`.
-/
theorem NormLength.full : NormLength.Statement := NormLength.proof
/- English proof (translation)
The claim follows from `VertTermEq.proof`.
-/
theorem VertTermEq.full : VertTermEq.Statement := VertTermEq.proof
/- English proof (translation)
The claim follows from `PrimitiveUnit.proof`.
-/
theorem PrimitiveUnit.full : PrimitiveUnit.Statement := PrimitiveUnit.proof
/- English proof (translation)
The claim follows from `ParAlgIndep.proof`.
-/
theorem ParAlgIndep.full : ParAlgIndep.Statement := ParAlgIndep.proof
/- English proof (translation)
The claim follows from `NormFormEval.proof`.
-/
theorem NormFormEval.full : NormFormEval.Statement := NormFormEval.proof
/- English proof (translation)
The claim follows from `ChartTorsion.proof`.
-/
theorem ChartTorsion.full : ChartTorsion.Statement := ChartTorsion.proof
/- English proof (translation)
The claim follows from `ChowFormHomog.proof`.
-/
theorem ChowFormHomog.full : ChowFormHomog.Statement := ChowFormHomog.proof
/- English proof (translation)
The claim follows from `IncidenceNull.proof`.
-/
theorem IncidenceNull.full : IncidenceNull.Statement := IncidenceNull.proof
/- English proof (translation)
The claim follows from `LengthDecomp.proof`.
-/
theorem LengthDecomp.full : LengthDecomp.Statement := LengthDecomp.proof
/- English proof (translation)
The claim follows from `NormFormLocalization.proof`.
-/
theorem NormFormLocalization.full : NormFormLocalization.Statement := NormFormLocalization.proof
/- English proof (translation)
The claim follows from `ParDVRIsDVR.proof`.
-/
theorem ParDVRIsDVR.full : ParDVRIsDVR.Statement := ParDVRIsDVR.proof
/- English proof (translation)
The claim follows from `ParFracIsFractionRing.proof`.
-/
theorem ParFracIsFractionRing.full : ParFracIsFractionRing.Statement := ParFracIsFractionRing.proof
/- English proof (translation)
The claim follows from `PrimitiveScale.proof`.
-/
theorem PrimitiveScale.full : PrimitiveScale.Statement := PrimitiveScale.proof
/- English proof (translation)
The claim follows from `SecBGeneric.proof`.
-/
theorem SecBGeneric.full : SecBGeneric.Statement := SecBGeneric.proof
/- English proof (translation)
The claim follows from `SecBFinite.proof IncidenceNull.full ChartTorsion.full PrimitiveScale.full`.
-/
theorem SecBFinite.full : SecBFinite.Statement :=
  SecBFinite.proof IncidenceNull.full ChartTorsion.full PrimitiveScale.full

end GroundTheory.Heights₂.Heights.Vertical
