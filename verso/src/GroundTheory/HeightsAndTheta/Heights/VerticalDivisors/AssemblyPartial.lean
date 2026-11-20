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
A detailed English derivation is pending.
-/
theorem NormLength.full : NormLength.Statement := NormLength.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem VertTermEq.full : VertTermEq.Statement := VertTermEq.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PrimitiveUnit.full : PrimitiveUnit.Statement := PrimitiveUnit.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ParAlgIndep.full : ParAlgIndep.Statement := ParAlgIndep.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NormFormEval.full : NormFormEval.Statement := NormFormEval.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChartTorsion.full : ChartTorsion.Statement := ChartTorsion.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ChowFormHomog.full : ChowFormHomog.Statement := ChowFormHomog.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem IncidenceNull.full : IncidenceNull.Statement := IncidenceNull.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem LengthDecomp.full : LengthDecomp.Statement := LengthDecomp.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem NormFormLocalization.full : NormFormLocalization.Statement := NormFormLocalization.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ParDVRIsDVR.full : ParDVRIsDVR.Statement := ParDVRIsDVR.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ParFracIsFractionRing.full : ParFracIsFractionRing.Statement := ParFracIsFractionRing.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PrimitiveScale.full : PrimitiveScale.Statement := PrimitiveScale.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SecBGeneric.full : SecBGeneric.Statement := SecBGeneric.proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SecBFinite.full : SecBFinite.Statement :=
  SecBFinite.proof IncidenceNull.full ChartTorsion.full PrimitiveScale.full

end GroundTheory.Heights₂.Heights.Vertical
