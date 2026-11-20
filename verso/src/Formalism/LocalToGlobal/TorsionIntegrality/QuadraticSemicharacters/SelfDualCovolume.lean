import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyPhaseQuadratic
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaussSumEighthPower
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnitaryEighthOf
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.RelIndexEqAbsDetReal
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionActionPermutesPlaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GaloisDescentSubspaces
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionInterSubspace
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ExtensionFiltrationStable
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyGaussianIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DiagonalIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnfoldingIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.SelfDualCovolumeProof
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DifferentialRepresentation
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.GapStatement
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.TripleSumEighthOf
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.TripleEighthProof

namespace Formalism.L2.Th1.H

/- English proof (translation)
The claim follows from `unitary_index`.
-/
theorem unitaryIndex : UnitaryIndex := unitary_index
/- English proof (translation)
The claim follows from `cayleyPhaseBasic`.
-/
theorem phiBasic : PhiBasic := cayleyPhaseBasic
/- English proof (translation)
The claim follows from `gaussSumEighthPower`.
-/
theorem gaussEighth : GaussEighth := gaussSumEighthPower
/- English proof (translation)
The claim follows from `UnitaryGauss_of gaussEighth`.
-/
theorem unitaryGauss : UnitaryGauss := UnitaryGauss_of gaussEighth
/- English proof (translation)
The claim follows from `cayleyDet`.
-/
theorem detCayley : DetCayley := cayleyDet
/- English proof (translation)
The claim follows from `UnitaryConstant_proof`.
-/
theorem unitaryConstant : UnitaryConstant := UnitaryConstant_proof
/- English proof (translation)
The claim follows from `UnitaryEighth_proof`.
-/
theorem unitaryEighth : UnitaryEighth := UnitaryEighth_proof

/- English proof (translation)
The claim follows from `TripleFormula_proof`.
-/
theorem tripleFormula : TripleFormula := TripleFormula_proof
/- English proof (translation)
The claim follows from `triplePhaseQuadratic`.
-/
theorem psiQuadratic : PsiQuadratic := triplePhaseQuadratic
/- English proof (translation)
The claim follows from `TripleEighth_proof`.
-/
theorem tripleEighth : TripleEighth := TripleEighth_proof

end Formalism.L2.Th1.H
