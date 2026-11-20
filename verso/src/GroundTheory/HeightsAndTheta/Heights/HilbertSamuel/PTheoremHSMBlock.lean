import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsArith
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsReductionToProjectiveBlock
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsSupBoundBlock
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.GeometryOfNumbersTheory Filter Asymptotics

noncomputable section

/- English proof (translation)
Introduce `D K _ _ ι _ Ω _ _ I d hI`. Use `⟨?_, hS D K ι Ω d⟩` and prove the remaining obligations. Establish `h1` using `hR D K ι Ω I d hI`. Establish `h2` using `(hP D I hI).const_mul_left (genDeg (mCoordIdeal d.y) D d.A.a : ℝ)`. Use `(h1.add h2).congr_left fun n => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem TheoremHSMBlock.proof (hR : ReductionToProjectiveBlock.Statement)
    (hP : HilbertSamuelProjective.Statement) (hS : SupBoundBlock.Statement) :
    TheoremHSMBlock.Statement := by
  intro D K _ _ ι _ Ω _ _ I d hI
  refine ⟨?_, hS D K ι Ω d⟩
  have h1 := hR D K ι Ω I d hI
  have h2 := (hP D I hI).const_mul_left (genDeg (mCoordIdeal d.y) D d.A.a : ℝ)
  refine (h1.add h2).congr_left fun n => ?_
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
