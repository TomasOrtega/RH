import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsMoreAlt
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsSide
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

/- English proof (translation)
Introduce `F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n`. Substitute `hx` using the available equality. Conclude with `ModelDimEq.full F K ι Ω y k₀ N e hmod n`.
-/
theorem ModelDim.proof : ModelDim.Statement := by
  intro F _ K _ _ ι _ Ω _ _ y k₀ N e x hx hmod n
  subst hx
  exact ModelDimEq.full F K ι Ω y k₀ N e hmod n

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
