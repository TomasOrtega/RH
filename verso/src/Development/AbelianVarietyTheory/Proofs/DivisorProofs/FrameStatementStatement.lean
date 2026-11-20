import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FrameOf.frameSt_of_smallSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFrameStatement.lean&line=267#L267)
-/
theorem _root_.GlobalTheory.T.FrameStatement : SmallSt → FrameSt := by
  first | exact @GlobalTheory.FrameOf.frameSt_of_smallSt | exact GlobalTheory.FrameOf.frameSt_of_smallSt | (intros; apply GlobalTheory.FrameOf.frameSt_of_smallSt <;> assumption)
