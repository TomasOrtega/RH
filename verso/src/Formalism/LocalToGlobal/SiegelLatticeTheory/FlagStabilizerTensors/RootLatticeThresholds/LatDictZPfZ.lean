import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.ZOrbitOfOpen
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZPlane
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LatDictZGlue

namespace Formalism.L2.SG.Pf.LatDictZ

/- English proof (translation)
The claim follows from `zOrbit_of_open Z2.primitive_plane_local Z5.adelic_gluing`.
-/
theorem anisotropic_vector_orbit : LatDictZ.ZOrbit :=
  zOrbit_of_open Z2.primitive_plane_local Z5.adelic_gluing

end Formalism.L2.SG.Pf.LatDictZ
