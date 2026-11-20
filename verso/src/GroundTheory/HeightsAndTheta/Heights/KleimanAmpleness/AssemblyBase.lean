import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechDSq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDegLocExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechExact
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechFlat
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechCone
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCechTransport
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurent
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePolyLaurentCohom
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerrePoly
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedPres
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGradedULift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCohomRetract
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreOnto
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSerreTail
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteTwists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistSections
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PProjDegreePositive
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPositive
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PHilbertPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PVeryAmpleTwistGenerated
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleCover
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PAmpleTwistLocal
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PGeneratedAmple
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeAway
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThreeOnW
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepThree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationExists
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltration
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationPoint
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PPrimeFiltrationRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestriction
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrictTwist
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PStepDataJProper
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSubvarDrop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PConservationOfDegree
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PNefGeneric
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PDomination
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCountDrop
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionCount
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u v w

/- English proof (translation)
The claim follows from `CechDSq.proof`.
-/
theorem CechDSq.full : CechDSq.Statement.{u, v} := CechDSq.proof
/- English proof (translation)
The claim follows from `DegLocExact.proof`.
-/
theorem DegLocExact.full : DegLocExact.Statement.{u, v} := DegLocExact.proof
/- English proof (translation)
The claim follows from `CechExact.proof CechDSq.full DegLocExact.full`.
-/
theorem CechExact.full : CechExact.Statement.{u, v} := CechExact.proof CechDSq.full DegLocExact.full
/- English proof (translation)
The claim follows from `CechTop.proof`.
-/
theorem CechTop.full : CechTop.Statement.{u, v} := CechTop.proof
/- English proof (translation)
The claim follows from `CechFlat.proof`.
-/
theorem CechFlat.full : CechFlat.Statement.{u, v} := CechFlat.proof
/- English proof (translation)
The claim follows from `Cech.Cone.proof`.
-/
theorem Cech.Cone.full : Cech.Cone.Statement.{u, v} := Cech.Cone.proof
/- English proof (translation)
The claim follows from `Cech.Transport.proof`.
-/
theorem Cech.Transport.full : Cech.Transport.Statement.{u, v, w} := Cech.Transport.proof
/- English proof (translation)
The claim follows from `SerrePoly.Laurent.proof`.
-/
theorem SerrePoly.Laurent.full : SerrePoly.Laurent.Statement.{u} := SerrePoly.Laurent.proof
/- English proof (translation)
The claim follows from `SerrePoly.LaurentCohom.proof Cech.Cone.full`.
-/
theorem SerrePoly.LaurentCohom.full : SerrePoly.LaurentCohom.Statement.{u} :=
  SerrePoly.LaurentCohom.proof Cech.Cone.full
/- English proof (translation)
The claim follows from `SerrePoly.proof SerrePoly.Laurent.full Cech.Transport.full SerrePoly.LaurentCohom.full`.
-/
theorem SerrePoly.full : SerrePoly.Statement.{u} :=
  SerrePoly.proof SerrePoly.Laurent.full Cech.Transport.full SerrePoly.LaurentCohom.full
/- English proof (translation)
The claim follows from `SerreFree.proof SerrePoly.full`.
-/
theorem SerreFree.full : SerreFree.Statement.{u, v} := SerreFree.proof SerrePoly.full
/- English proof (translation)
The claim follows from `GradedPres.proof`.
-/
theorem GradedPres.full : GradedPres.Statement.{u, v} := GradedPres.proof
/- English proof (translation)
The claim follows from `GradedULift.proof`.
-/
theorem GradedULift.full : GradedULift.Statement.{u, v} := GradedULift.proof
/- English proof (translation)
The claim follows from `CohomRetract.proof`.
-/
theorem CohomRetract.full : CohomRetract.Statement.{u, v, w} := CohomRetract.proof

/- English proof (translation)
The claim follows from `SerreFinite.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full CohomRetract.full`.
-/
theorem SerreFinite.full : SerreFinite.Statement.{u, v} :=
  SerreFinite.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

/- English proof (translation)
The claim follows from `SerreVanish.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full CohomRetract.full`.
-/
theorem SerreVanish.full : SerreVanish.Statement.{u, v} :=
  SerreVanish.proof CechExact.full CechTop.full SerreFree.full GradedPres.full GradedULift.full
    CohomRetract.full

/- English proof (translation)
The claim follows from `SerreOnto.proof CechExact.full SerreFree.full SerreVanish.full`.
-/
theorem SerreOnto.full : SerreOnto.Statement.{u, v} :=
  SerreOnto.proof CechExact.full SerreFree.full SerreVanish.full

/- English proof (translation)
The claim follows from `SerreTail.proof SerreFinite.full SerreOnto.full`.
-/
theorem SerreTail.full : SerreTail.Statement.{u, v} := SerreTail.proof SerreFinite.full SerreOnto.full

/- English proof (translation)
The claim follows from `Extension.proof`.
-/
theorem Extension.full : Extension.Statement.{u, v, w} := Extension.proof
/- English proof (translation)
The claim follows from `Generated.proof Extension.full`.
-/
theorem Generated.full : Generated.Statement.{u, w} := Generated.proof Extension.full
/- English proof (translation)
The claim follows from `TwistFinite.proof Extension.full SerreFinite.full`.
-/
theorem TwistFinite.full : TwistFinite.Statement.{u, w} := TwistFinite.proof Extension.full SerreFinite.full
/- English proof (translation)
The claim follows from `FiniteTwists.proof TwistFinite.full`.
-/
theorem FiniteTwists.full : FiniteTwists.Statement.{u, w} := FiniteTwists.proof TwistFinite.full
/- English proof (translation)
The claim follows from `TwistSections.proof SerreOnto.full`.
-/
theorem TwistSections.full : TwistSections.Statement.{u, w} := TwistSections.proof SerreOnto.full
/- English proof (translation)
The claim follows from `ProjDegreePositive.proof`.
-/
theorem ProjDegreePositive.full : ProjDegreePositive.Statement.{u} := ProjDegreePositive.proof
/- English proof (translation)
The claim follows from `HilbertPositive.proof ProjDegreePositive.full TwistSections.full`.
-/
theorem HilbertPositive.full : HilbertPositive.Statement.{u, w} :=
  HilbertPositive.proof ProjDegreePositive.full TwistSections.full
/- English proof (translation)
The claim follows from `HilbertPoint.proof`.
-/
theorem HilbertPoint.full : HilbertPoint.Statement.{u, w} := HilbertPoint.proof
/- English proof (translation)
The claim follows from `PrimeFiltration.Exists.proof`.
-/
theorem PrimeFiltration.Exists.full : PrimeFiltration.Exists.Statement.{u, v, w} :=
  PrimeFiltration.Exists.proof
/- English proof (translation)
The claim follows from `PrimeFiltration.proof PrimeFiltration.Exists.full`.
-/
theorem PrimeFiltration.full : PrimeFiltration.Statement.{u, v, w} :=
  PrimeFiltration.proof PrimeFiltration.Exists.full
/- English proof (translation)
The claim follows from `PrimeFiltration.Irrelevant.proof`.
-/
theorem PrimeFiltration.Irrelevant.full : PrimeFiltration.Irrelevant.Statement.{u} :=
  PrimeFiltration.Irrelevant.proof
/- English proof (translation)
The claim follows from `PrimeFiltration.Point.proof`.
-/
theorem PrimeFiltration.Point.full : PrimeFiltration.Point.Statement.{u, w} := PrimeFiltration.Point.proof
/- English proof (translation)
The claim follows from `PrimeFiltration.Restrict.proof`.
-/
theorem PrimeFiltration.Restrict.full : PrimeFiltration.Restrict.Statement.{u, w} :=
  PrimeFiltration.Restrict.proof
/- English proof (translation)
The claim follows from `Restriction.proof`.
-/
theorem Restriction.full : Restriction.Statement.{u, w} := Restriction.proof

/- English proof (translation)
The claim follows from `VeryAmpleTwistGenerated.proof`.
-/
theorem VeryAmpleTwistGenerated.full : VeryAmpleTwistGenerated.Statement.{u, w} :=
  VeryAmpleTwistGenerated.proof
/- English proof (translation)
The claim follows from `AmpleCover.proof`.
-/
theorem AmpleCover.full : AmpleCover.Statement.{u, w} := AmpleCover.proof
/- English proof (translation)
The claim follows from `StepThree.Away.proof`.
-/
theorem StepThree.Away.full : StepThree.Away.Statement.{u, w} := StepThree.Away.proof
/- English proof (translation)
The claim follows from `RestrictTwist.proof`.
-/
theorem RestrictTwist.full : RestrictTwist.Statement.{u, w} := RestrictTwist.proof
/- English proof (translation)
The claim follows from `StepData.JProper.proof`.
-/
theorem StepData.JProper.full : StepData.JProper.Statement.{u, w} := StepData.JProper.proof
/- English proof (translation)
The claim follows from `SubvarDrop.proof`.
-/
theorem SubvarDrop.full : SubvarDrop.Statement.{u, w} := SubvarDrop.proof

/- English proof (translation)
The claim follows from `AmpleTwistLocal.proof hA`.
-/
theorem AmpleTwistLocal.assembled (hA : AmpleAffineGen.Statement.{u, w}) :
    AmpleTwistLocal.Statement.{u, w} :=
  AmpleTwistLocal.proof hA

/- English proof (translation)
The claim follows from `GeneratedAmple.proof AmpleCover.full (AmpleTwistLocal.assembled hA)`.
-/
theorem GeneratedAmple.assembled (hA : AmpleAffineGen.Statement.{u, w}) :
    GeneratedAmple.Statement.{u, w} :=
  GeneratedAmple.proof AmpleCover.full (AmpleTwistLocal.assembled hA)

/- English proof (translation)
The claim follows from `TwistVanish.proof Extension.full SerreVanish.full hS`.
-/
theorem TwistVanish.assembled (hS : TwistSplit.Statement.{u, w}) : TwistVanish.Statement.{u, w} :=
  TwistVanish.proof Extension.full SerreVanish.full hS

/- English proof (translation)
The claim follows from `NefRestrict.proof RestrictTwist.full hRL`.
-/
theorem NefRestrict.assembled (hRL : RestrLenRestrict.Statement.{u, w}) : NefRestrict.Statement.{u, w} :=
  NefRestrict.proof RestrictTwist.full hRL

/- English proof (translation)
The claim follows from `FiniteSections.proof Extension.full hT`.
-/
theorem FiniteSections.assembled (hT : TildeTail.Statement.{u, w}) : FiniteSections.Statement.{u, w} :=
  FiniteSections.proof Extension.full hT

/- English proof (translation)
The claim follows from `Domination.proof (FiniteSections.assembled hT)`.
-/
theorem Domination.assembled (hT : TildeTail.Statement.{w, w}) : Domination.Statement.{u, w} :=
  Domination.proof (FiniteSections.assembled hT)

/- English proof (translation)
The claim follows from `SurjectiveClosed.proof Extension.full hFam hVan`.
-/
theorem SurjectiveClosed.assembled (hFam : IdealTwistFamily.Statement.{u, w})
    (hVan : TildeVanish.Statement.{u, w, w}) : SurjectiveClosed.Statement.{u, w} :=
  SurjectiveClosed.proof Extension.full hFam hVan

/- English proof (translation)
The claim follows from `ConservationOfDegree.proof hA hB`.
-/
theorem ConservationOfDegree.assembled (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : ConservationOfDegree.Statement.{u, w} :=
  ConservationOfDegree.proof hA hB

/- English proof (translation)
The claim follows from `NefGeneric.proof (ConservationOfDegree.assembled hA hB)`.
-/
theorem NefGeneric.assembled (hA : FibreHilbertFlat.Statement.{u, w})
    (hB : FibreCycleDegree.Statement.{u, w}) : NefGeneric.Statement.{u, w} :=
  NefGeneric.proof (ConservationOfDegree.assembled hA hB)

/- English proof (translation)
The claim follows from `SectionCount.Drop.proof hF hT hH hR`.
-/
theorem SectionCount.Drop.assembled (hF : SectionCount.Drop.Filt.Statement.{u, w})
    (hT : SectionCount.Drop.Term.Statement.{u, w}) (hH : SectionCount.Drop.HilbW.Statement.{u, w})
    (hR : GenericPointSectionInput.Statement.{u, w}) : SectionCount.Drop.Statement.{u, w} :=
  SectionCount.Drop.proof hF hT hH hR

/- English proof (translation)
The claim follows from `SectionCount.proof hTop (SectionCount.Drop.assembled hF hT hH hR)`.
-/
theorem SectionCount.assembled (hTop : SectionCount.Top.Statement.{u, w})
    (hF : SectionCount.Drop.Filt.Statement.{u, w}) (hT : SectionCount.Drop.Term.Statement.{u, w})
    (hH : SectionCount.Drop.HilbW.Statement.{u, w}) (hR : GenericPointSectionInput.Statement.{u, w}) :
    SectionCount.Statement.{u, w} :=
  SectionCount.proof hTop (SectionCount.Drop.assembled hF hT hH hR)

/- English proof (translation)
The claim follows from `StepThree.proof StepThree.Away.full (StepThree.OnW.proof hL hG)`.
-/
theorem StepThree.assembled (hL : StepThree.OnW.Lift.Statement.{u, w})
    (hG : StepThree.OnW.Gen.Statement.{u, w}) : StepThree.Statement.{u, w} :=
  StepThree.proof StepThree.Away.full (StepThree.OnW.proof hL hG)

end GroundTheory.Heights₂.Heights.Kleiman
