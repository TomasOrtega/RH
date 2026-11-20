import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Assembly
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereLawBasic
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PSphereLawFirstCoord
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SphereLawBasic.full : SphereLawBasic.Statement := SphereLawBasic.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SphereLawFirstCoord.full : SphereLawFirstCoord.Statement := SphereLawFirstCoord.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem FibreMahlerForms.full : FibreMahlerForms.Statement := FibreMahlerForms.proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SpherePhase.full : SpherePhase.Statement :=
  SpherePhase.full_of_sphereLawBasic SphereLawBasic.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem SphereProjectionLaw.full : SphereProjectionLaw.Statement :=
  SphereProjectionLaw.full_of SphereLawBasic.full SphereLawFirstCoord.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem PointwiseLelong.full : PointwiseLelong.Statement :=
  PointwiseLelong.full_of SphereLawBasic.full SphereLawFirstCoord.full

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem HeightOfCycle.full : HeightOfCycle.Statement :=
  HeightOfCycle.full_of_fibreMahlerForms FibreMahlerForms.full

end GroundTheory.Heights₂.Heights
