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
The claim follows from `Formalism.GrowthSums.segment_bound_holds`.
-/
theorem segmentBound : Formalism.GrowthSums.SegmentBound := Formalism.GrowthSums.segment_bound_holds
/- English proof (translation)
The claim follows from `Formalism.GrowthSums.next_even_top_holds`.
-/
theorem nextEvenTop : Formalism.GrowthSums.NextEvenTop := Formalism.GrowthSums.next_even_top_holds
/- English proof (translation)
The claim follows from `Formalism.GrowthSums.top_count_holds`.
-/
theorem topCount : Formalism.GrowthSums.TopCount := Formalism.GrowthSums.top_count_holds

end Formalism.GrowthSums.Top
