import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.PKHTheoremSAux
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman

open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ M _ _ _ _ N _ _ _ _ 𝓜 𝓝 g c n hg`. Use `⟨fun φ hφ => Submodule.mem_pi.mpr fun I _ => ?_, LinearMap.ext fun z => ?_⟩` and prove the remaining obligations. Conclude with `KHTheoremS.locMap_mem_locPart hg (Submodule.mem_pi.mp hφ I (Set.mem_univ _))`. Conclude with `KHTheoremS.cechD_cechMap g n z`.
-/
theorem KHCechMapDeg.full : KH.CechMapDegStatement := by
  intro S _ K _ _ ι _ _ M _ _ _ _ N _ _ _ _ 𝓜 𝓝 g c n hg
  refine ⟨fun φ hφ => Submodule.mem_pi.mpr fun I _ => ?_, LinearMap.ext fun z => ?_⟩
  · exact KHTheoremS.locMap_mem_locPart hg (Submodule.mem_pi.mp hφ I (Set.mem_univ _))
  · exact KHTheoremS.cechD_cechMap g n z

end GroundTheory.Heights₂.Heights.Kleiman
