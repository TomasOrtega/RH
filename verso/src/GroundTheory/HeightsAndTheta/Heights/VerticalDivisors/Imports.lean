import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.OfFreeParAlgIndep
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PFreeParAlgIndep
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

/- English proof (translation)
The claim follows from `FreeParAlgIndep.proof`.
-/
theorem FreeParAlgIndep.full : FreeParAlgIndep.Statement := FreeParAlgIndep.proof

/- English proof (translation)
The claim follows from `SecPointSeparable.of_freeParAlgIndep FreeParAlgIndep.full`.
-/
theorem SecPointSeparable.full : SecPointSeparable.Statement :=
  SecPointSeparable.of_freeParAlgIndep FreeParAlgIndep.full

/- English proof (translation)
The claim follows from `GenSecSeparable.of_freeParAlgIndep FreeParAlgIndep.full`.
-/
theorem GenSecSeparable.full : GenSecSeparable.Statement :=
  GenSecSeparable.of_freeParAlgIndep FreeParAlgIndep.full

/- English proof (translation)
The claim follows from `SpecLength.of_freeParAlgIndep FreeParAlgIndep.full`.
-/
theorem SpecLength.full : SpecLength.Statement :=
  SpecLength.of_freeParAlgIndep FreeParAlgIndep.full

/- English proof (translation)
The claim follows from `ChowFormSectionVertical.of_freeParAlgIndep FreeParAlgIndep.full`.
-/
theorem ChowFormSectionVertical.full : ChowFormSectionVertical.Statement :=
  ChowFormSectionVertical.of_freeParAlgIndep FreeParAlgIndep.full

end GroundTheory.Heights₂.Heights.Vertical
