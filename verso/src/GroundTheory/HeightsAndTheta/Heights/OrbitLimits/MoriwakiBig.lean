import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StatementsMoriwakiBigCurve
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Targets

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

/- English proof (translation)
Introduce `K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen`. Break down `Nat.eq_zero_or_pos D with rfl | hD` into its components or cases. Conclude with `hC K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen`. Conclude with `hG6 K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc`.
-/
theorem MoriwakiBig.of_found (hG6 : HilbertSamuel.ArithmeticVolumeBig.Statement) (hC : MoriwakiBigCurve.Statement) :
    ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.MoriwakiBigStatement := by
  intro K _ ι _ Ω _ y D A P0 II hII har hb hP0 hs hc hnef hgen
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · exact hC K ι Ω y A P0 II hII har hb hP0 hs hc hnef hgen
  · exact hG6 K ι Ω y D A P0 II hD hII har hb hP0 hs hnef hc

end GroundTheory.Heights₂.Heights.Targets
