import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.KernelFromKOne
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WModel
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.WChain
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.FrobeniusLiftNorms.EGaussK
import Mathlib
import Formalism.ThetaLogCoordinates.UniformThetaSubstitution.EdgeExponent

namespace Formalism.InvariantFactorPaths.G7.Top

open Formalism.InvariantFactorPaths.G7

/- English proof (translation)
The claim follows from `modelExists_statement`.
-/
theorem modelExists : ModelExists := modelExists_statement
/- English proof (translation)
The claim follows from `BetaNonVacuous_of modelExists lawExists gcIsBeta gcUnique`.
-/
theorem betaNonVacuous : BetaNonVacuous := BetaNonVacuous_of modelExists lawExists gcIsBeta gcUnique
/- English proof (translation)
The claim follows from `chainModel_statement`.
-/
theorem chainModel : ChainModel := chainModel_statement

/- English proof (translation)
The claim follows from `kernel_bounds_generic`.
-/
theorem kernel_from_k_one_k : KernelBoundsGeneric := kernel_bounds_generic

end Formalism.InvariantFactorPaths.G7.Top
