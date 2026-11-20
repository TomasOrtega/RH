import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairThetaLiftFactorsThroughIntertwiner
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FPairThetaLiftFactorsThroughIntertwiner.lean&line=270#L270)
-/
theorem _root_.GlobalTheory.T.pairThetaLift_factors_through_intertwiner : ∀ (D : D7) (X : ProvA), Inputs D X → CuspAll D X → PairLifts D X := by
  first | exact @GlobalTheory.PairLift.RuleLift.pairLifts | exact GlobalTheory.PairLift.RuleLift.pairLifts | (intros; apply GlobalTheory.PairLift.RuleLift.pairLifts <;> assumption)
