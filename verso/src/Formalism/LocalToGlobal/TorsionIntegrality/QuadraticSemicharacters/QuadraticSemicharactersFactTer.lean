import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.StdDataCmProof
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.FinitelyGeneratedModPow
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.ScalePairMulMulEq

namespace Formalism.L2.Th1.H

/- English proof (translation)
The claim follows from `StdDataCm_proof`.
-/
theorem stdDataCm : StdDataCm := StdDataCm_proof
/- English proof (translation)
The claim follows from `KernelRatio_of unitaryConstant`.
-/
theorem kernelRatio : KernelRatio := KernelRatio_of unitaryConstant

/- English proof (translation)
The claim follows from `quadraticSemicharacterIdentityReformulated_of_kernelRatio_of_localStandard_of_kappaExists kernelRatio hL hκ`.
-/
theorem quadraticSemicharacters_of_fact (hL : LocalStandard) (hκ : KappaExists) : quadraticSemicharacterIdentityReformulated := quadraticSemicharacterIdentityReformulated_of_kernelRatio_of_localStandard_of_kappaExists kernelRatio hL hκ

end Formalism.L2.Th1.H
