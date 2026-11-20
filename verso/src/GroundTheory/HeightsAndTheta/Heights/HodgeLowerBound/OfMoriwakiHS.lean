import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.MoriwakiSt
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PtsIntegralCurveConst
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PNefOnGenericOfSemipos
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PCurvePointsFinite
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsBirationalModelExists
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry GroundTheory.Heights₂.Heights.HilbertSamuel Filter Topology

/- English proof (translation)
Introduce `K _ ι _ P P0 D A II hII hP hP0 hsemi hnef hconj hW`. Take `⟨Ω, _, y, hyP, hbir⟩` from `hB K ι P (D + 1) hP`. Substitute `hyP` using the available equality. Establish `hgen : NefOnGeneric (mCoordIdeal y) A` using `NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hP0 hsemi`. Establish `hlim` using `hM K ι Ω y D A P0 II hII hP hbir hP0 hsemi hconj hnef hgen hW`.

Use `ge_of_tendsto' hlim fun n => div_nonneg ?_ ?_` and prove the remaining obligations. Conclude with `Real.log_natCast_nonneg _`. Check the signs of the components of the expression.
-/
theorem ArithKleiman.of_moriwakiHS (hM : MoriwakiHSStatement) (hB : BirationalModelExists.Statement) :
    ArithKleiman.Statement := by
  intro K _ ι _ P P0 D A II hII hP hP0 hsemi hnef hconj hW
  obtain ⟨Ω, _, y, hyP, hbir⟩ := hB K ι P (D + 1) hP
  subst hyP
  have hgen : NefOnGeneric (mCoordIdeal y) A :=
    NefOnGenericOfSemipos.proof K ι (mCoordIdeal y) P0 A hP0 hsemi
  have hlim := hM K ι Ω y D A P0 II hII hP hbir hP0 hsemi hconj hnef hgen hW
  refine ge_of_tendsto' hlim fun n => div_nonneg ?_ ?_
  · exact Real.log_natCast_nonneg _
  · positivity

/- English proof (translation)
The claim follows from `G5.proof' (ArithKleiman.of_moriwakiHS hM hB) CurvePointsFinite.proof`.
-/
theorem Z1.proof (hM : MoriwakiHSStatement) (hB : BirationalModelExists.Statement) : SuccessiveMinimaLowerBound :=
  G5.proof' (ArithKleiman.of_moriwakiHS hM hB) CurvePointsFinite.proof

end GroundTheory.Heights₂.Heights.LowerBoundFree
