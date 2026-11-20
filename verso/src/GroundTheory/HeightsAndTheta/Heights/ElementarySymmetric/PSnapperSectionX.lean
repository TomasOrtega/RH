import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistTilde
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeShift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFiniteE
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSubquotFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotAdd
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotFiltX
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotIsoX
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubFamilyTwistX
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotDevissage
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PMulQuotEq
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionNonvanish
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSectionMulInj
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSection
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

universe u w

namespace SnapperSectionClosed

/- English proof (translation)
The claim follows from `SnapperFinite.proof Extension.full Extension.full TwistTilde.proof TwistTilde.proof TildeShift.proof (TildeFiniteE.proof SerreFinite.full)`.
-/
theorem snapperFinite : SnapperFinite.Statement.{u, w, w} :=
  SnapperFinite.proof Extension.full Extension.full TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

/- English proof (translation)
The claim follows from `SnapperQuotAdd.proof (SnapperSubquotFinite.proof snapperFinite)`.
-/
theorem quotAdd : SnapperQuotAdd.Statement.{u, w, w} :=
  SnapperQuotAdd.proof (SnapperSubquotFinite.proof snapperFinite)

/- English proof (translation)
The claim follows from `SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof quotAdd SubFamilyTwist.proof`.
-/
theorem quotDevissage : SnapperQuotDevissage.Statement.{u, w, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof quotAdd SubFamilyTwist.proof

end SnapperSectionClosed

open SnapperSectionClosed in

/- English proof (translation)
The claim follows from `SnapperSection.proof quotAdd quotDevissage MulQuotEq.proof SectionNonvanish.proof SectionMulInj.proof`.
-/
theorem SnapperSection.full : SnapperSection.Statement.{u, w} :=
  SnapperSection.proof quotAdd quotDevissage MulQuotEq.proof SectionNonvanish.proof SectionMulInj.proof

end GroundTheory.Heights₂.Heights.Kleiman
