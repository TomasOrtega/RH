import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.GlobalBoundRefinements

open NumberField

namespace Formalism.DivisionValues

/- English proof (translation)
The claim follows from `divisor_inequality_explicit`.
-/
theorem divIneqRecord : DivIneqRecord := divisor_inequality_explicit

/- English proof (translation)
The claim follows from `good_twisted_lattice`.
-/
theorem goodTwist : GoodTwist := good_twisted_lattice

end Formalism.DivisionValues
