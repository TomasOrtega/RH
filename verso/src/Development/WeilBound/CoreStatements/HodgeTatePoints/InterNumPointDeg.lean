import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFilt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PCycleSplitFiltStep
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSurjectiveClosed
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PIdealTwistFamily
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeVanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PFiniteSections
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeTail
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PCutRestrLenExact
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumCut
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PInterNumPointDeg
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PInterNumRestrict
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PRestrLenRestrict
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PRestrictQuotX

namespace PositivityTheory.HtPt.Kra

open GroundTheory.Heights₂.Heights.Kleiman

universe u w

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem surjectiveClosed : SurjectiveClosed.Statement.{u, w} :=
  SurjectiveClosed.proof Extension.proof IdealTwistFamily.proof (TildeVanish.proof SerreVanish.full)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finiteSections : FiniteSections.Statement.{u, w} :=
  FiniteSections.proof Extension.proof (TildeTail.proof SerreTail.full)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumberCut_of_mixedTwistShift (h : MixedTwistShift.Statement.{u, w}) : InterNumCut.Statement.{u, w} :=
  InterNumCut.proof (CycleSplit.Filt.proof (CycleSplit.Filt.Step.proof surjectiveClosed finiteSections))
    (CutRestrLenExact.proof surjectiveClosed finiteSections) h

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interNumPointDeg : InterNumPointDeg.Statement.{u, w} :=
  InterNumPointDeg.proof (InterNumRestrict.proof
    (RestrLenRestrict.proof surjectiveClosed PrimeFiltration.RestrictQuot.proof))

end PositivityTheory.HtPt.Kra
