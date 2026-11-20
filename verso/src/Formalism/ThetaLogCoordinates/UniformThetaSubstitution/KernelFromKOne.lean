import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KOneConsequence
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.OmegaOfTraceDuality
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.FrobeniusPartialCoboundaryBound
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.ExpansionsAtPlaces
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EGauss
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EKernel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EChain

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

/- English proof (translation)
The claim follows from `g_c_is_beta`.
-/
theorem gcIsBeta : GcIsBeta := g_c_is_beta
/- English proof (translation)
The claim follows from `g_c_unique`.
-/
theorem gcUnique : GcUnique := g_c_unique

end Formalism.InvariantFactorPaths.G7.Top
