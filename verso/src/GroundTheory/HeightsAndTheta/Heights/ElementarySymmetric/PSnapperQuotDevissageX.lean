import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperQuotDevissage
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperSubquotFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PSnapperFinite
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeFiniteE
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTwistTilde
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PTildeShift
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PExtension
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.AssemblyBase
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotFiltX
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSnapperQuotIsoX
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PSubFamilyTwistX
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

noncomputable section

universe u v w

/- English proof (translation)
The claim follows from `SnapperFinite.proof Extension.proof Extension.proof TwistTilde.proof TwistTilde.proof TildeShift.proof (TildeFiniteE.proof SerreFinite.full)`.
-/
theorem SnapperFinite.closed : SnapperFinite.Statement.{u, v, w} :=
  SnapperFinite.proof Extension.proof Extension.proof TwistTilde.proof TwistTilde.proof TildeShift.proof
    (TildeFiniteE.proof SerreFinite.full)

/- English proof (translation)
The claim follows from `SnapperSubquotFinite.proof SnapperFinite.closed`.
-/
theorem SnapperSubquotFinite.closed : SnapperSubquotFinite.Statement.{u, v, w} :=
  SnapperSubquotFinite.proof SnapperFinite.closed

/- English proof (translation)
The claim follows from `SnapperQuotAdd.proof SnapperSubquotFinite.closed`.
-/
theorem SnapperQuotAdd.closed : SnapperQuotAdd.Statement.{u, v, w} :=
  SnapperQuotAdd.proof SnapperSubquotFinite.closed

/- English proof (translation)
The claim follows from `SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof SnapperQuotAdd.closed SubFamilyTwist.proof`.
-/
theorem SnapperQuotDevissage.closed : SnapperQuotDevissage.Statement.{u, v, w} :=
  SnapperQuotDevissage.proof SnapperQuotFilt.proof SnapperQuotIso.proof SnapperQuotAdd.closed SubFamilyTwist.proof

end

end GroundTheory.Heights₂.Heights.Kleiman
