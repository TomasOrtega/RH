import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Assembly
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.AreaCmLNe
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.NormIntKur

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame

/- English proof (translation)
The claim follows from `hermFrame_of frobStep ratStep hL`.
-/
theorem hermFrame_of_locCore (hL : LocCore) : Formalism.L2.Th1.Top.FrP.HermFrame := hermFrame_of frobStep ratStep hL

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
