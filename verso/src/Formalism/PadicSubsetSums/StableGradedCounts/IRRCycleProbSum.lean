import Formalism.PadicSubsetSums.StableGradedCounts.IRRJoints
import Formalism.PadicSubsetSums.StableGradedCounts.IRRCycleProbPrime

namespace Formalism.IrreducibleCountingLemmas.GaloisIrreducibility

/- English proof (translation)
The claim follows from `cycleProbSum_of_cycleProbPrime prime_cycle_probability`.
-/
theorem prime_cycle_probability_sum : CycleProbSum := cycleProbSum_of_cycleProbPrime prime_cycle_probability

end Formalism.IrreducibleCountingLemmas.GaloisIrreducibility
