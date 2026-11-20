import Formalism.BranchSandwichDivisors.DivFromPassageAndNorm
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.GlobalBoundRefinements

namespace Formalism.BranchingDeterminantCap

/- English proof (translation)
The claim follows from `third_descent_inequality`.
-/
theorem stepDiiiRecord : StepDiiiRecord := third_descent_inequality
/- English proof (translation)
The claim follows from `chain_weights`.
-/
theorem chainWeights : ChainWeights := chain_weights

end Formalism.BranchingDeterminantCap
