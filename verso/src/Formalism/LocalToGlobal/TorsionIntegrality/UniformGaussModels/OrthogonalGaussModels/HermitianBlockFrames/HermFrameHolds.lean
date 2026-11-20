import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.IsUnitaryK
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.HermFrameOfLocCore
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.LocMain
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.RelativeIndexIdentityLatticeDiscSeven

namespace Formalism.L2.Th1.Top.FrP

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hermFrame_holds : HermFrame :=
  UnitaryGroupMassFormula.HermFrame.hermFrame_of_locCore UnitaryGroupMassFormula.HermFrame.Loc.local_core'

end Formalism.L2.Th1.Top.FrP
