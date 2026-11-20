import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGraphClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmplePow
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PLineTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistAlg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.LeadingCoeffPosCut
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleNefPlusAmple
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefProductNonneg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefPlusAmple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

/- English proof (translation)
The claim follows from `GraphClosed.proof`.
-/
theorem GraphClosed.full : GraphClosed.Statement.{u, w} := GraphClosed.proof
/- English proof (translation)
The claim follows from `VeryAmplePow.proof`.
-/
theorem VeryAmplePow.full : VeryAmplePow.Statement.{u, w} := VeryAmplePow.proof
/- English proof (translation)
The claim follows from `LineTwist.proof`.
-/
theorem LineTwist.full : LineTwist.Statement.{u, w} := LineTwist.proof
/- English proof (translation)
The claim follows from `TwistAlg.proof`.
-/
theorem TwistAlg.full : TwistAlg.Statement.{u, w} := TwistAlg.proof

/- English proof (translation)
The claim follows from `SectionExists.proof (SectionCount.assembled hTop hF hT hH hR) VeryAmplePow.full (LeadingCoeffPos.proof_of_cut hR hPos)`.
-/
theorem SectionExists.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) : SectionExists.Statement.{u, w} :=
  SectionExists.proof (SectionCount.assembled hTop hF hT hH hR) VeryAmplePow.full
    (LeadingCoeffPos.proof_of_cut hR hPos)

/- English proof (translation)
The claim follows from `VeryAmpleNefPlusAmple.proof Generated.full (SectionExists.assembled hTop hF hT hH hR hPos) (StepThree.assembled hL hG) GraphClosed.full hPt`.
-/
theorem VeryAmpleNefPlusAmple.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    VeryAmpleNefPlusAmple.Statement.{u, w} :=
  VeryAmpleNefPlusAmple.proof Generated.full (SectionExists.assembled hTop hF hT hH hR hPos)
    (StepThree.assembled hL hG) GraphClosed.full hPt

/- English proof (translation)
The claim follows from `NefProductNonneg.proof (VeryAmpleNefPlusAmple.assembled hTop hF hT hH hR hPos hL hG hPt) hR`.
-/
theorem NefProductNonneg.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    NefProductNonneg.Statement.{u, w} :=
  NefProductNonneg.proof (VeryAmpleNefPlusAmple.assembled hTop hF hT hH hR hPos hL hG hPt) hR

/- English proof (translation)
The claim follows from `NefPlusAmple.proof (GeneratedAmple.assembled hA) (VeryAmpleNefPlusAmple.assembled hTop hF hT hH hR hPos hL hG hPt) VeryAmpleTwistGenerated.full`.
-/
theorem NefPlusAmple.assembled (hA : AmpleAffineGen.Statement.{u, w})
    (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w})
    (hPos : VeryAmpleProductPos.Statement.{u, w}) (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) (hPt : PointGenerated.Statement.{u, w}) :
    NefPlusAmple.Statement.{u, w} :=
  NefPlusAmple.proof (GeneratedAmple.assembled hA)
    (VeryAmpleNefPlusAmple.assembled hTop hF hT hH hR hPos hL hG hPt) VeryAmpleTwistGenerated.full

end GroundTheory.Heights₂.Heights.Kleiman
