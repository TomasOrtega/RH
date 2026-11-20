import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLieActionFockOperatorsScalarsTrace.lean&line=685#L685)
-/
theorem _root_.GlobalTheory.T.lieAction_fockOperators_scalars_trace : ∀ D : D7, GlobalTheory.ChainFr.LieFockAll D := by
  first | exact @GlobalTheory.LieScalar.lieFockAll | exact GlobalTheory.LieScalar.lieFockAll | (intros; apply GlobalTheory.LieScalar.lieFockAll <;> assumption)
