import Formalism.GradedWeylDivisibility.FinalC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSIdxFinite
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.SSBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActDiagWeight
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.RowActMul
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLLe
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLKBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLDiag
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwMem
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.TensorBasis
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BlockActTensor

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sSIdxFinite : SSIdxFinite := semistandard_index_finite
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem sSBasis : SSBasis := semistandard_basis
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rowActDiagWeight : RowActDiagWeight := row_action_diagonal_weight
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem rowActMul : RowActMul := row_action_mul
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nablaLLe : NablaLLe := nabla_weight_le
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nablaLBasis : NablaLBasis := nablaLBasis_of rowActMul
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nablaLKBasis : NablaLKBasis := nablaLKBasis_of rowActMul sSBasis
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nablaLDiag : NablaLDiag := nablaLDiag_of rowActMul rowActDiagWeight nablaLBasis
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nablaLTwMem : NablaLTwMem := nabla_twist_mem
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tensorBasis : TensorBasis := tensor_power_basis
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem blockActTensor : BlockActTensor := block_action_tensor

end Formalism.GradedWeylDivisibility
