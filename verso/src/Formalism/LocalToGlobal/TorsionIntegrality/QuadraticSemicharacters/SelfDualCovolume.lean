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
A detailed English derivation is pending.
-/
theorem unitaryIndex : UnitaryIndex := unitary_index
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem phiBasic : PhiBasic := cayleyPhaseBasic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gaussEighth : GaussEighth := gaussSumEighthPower
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitaryGauss : UnitaryGauss := UnitaryGauss_of gaussEighth
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem detCayley : DetCayley := cayleyDet
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitaryConstant : UnitaryConstant := UnitaryConstant_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem unitaryEighth : UnitaryEighth := UnitaryEighth_proof

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tripleFormula : TripleFormula := TripleFormula_proof
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem psiQuadratic : PsiQuadratic := triplePhaseQuadratic
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tripleEighth : TripleEighth := TripleEighth_proof

end Formalism.L2.Th1.H
