import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmallStatement.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.SmallStatement : SmallSt := by
  first | exact @GlobalTheory.ExpTie.smallSt | exact GlobalTheory.ExpTie.smallSt | (intros; apply GlobalTheory.ExpTie.smallSt <;> assumption)
