import Formalism.GrowthSums.FactorialBaseGrowth.Coarse
import Formalism.GrowthSums.FactorialBaseGrowth.Harmonic
import Formalism.GrowthSums.FactorialBaseGrowth.QuadraticExponentIdentity
import Formalism.GrowthSums.FactorialBaseGrowth.Segment
import Formalism.GrowthSums.FactorialBaseGrowth.NextEvenTopHolds
import Formalism.GrowthSums.FactorialBaseGrowth.LogCoef
import Formalism.GrowthSums.FactorialBaseGrowth.Length
import Formalism.GrowthSums.FactorialBaseGrowth.KapPrime
import Mathlib
import Formalism.GrowthSums.FactorialBaseGrowth.PathBasisOfCount

namespace Formalism.GrowthSums.Top

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem segmentBound : Formalism.GrowthSums.SegmentBound := Formalism.GrowthSums.segment_bound_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nextEvenTop : Formalism.GrowthSums.NextEvenTop := Formalism.GrowthSums.next_even_top_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem topCount : Formalism.GrowthSums.TopCount := Formalism.GrowthSums.top_count_holds

end Formalism.GrowthSums.Top
