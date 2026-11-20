import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftsCuspidalOfLowerTowerLiftsVanish
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PairLift.cuspAll_of_lowAll` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FThetaLiftsCuspidalOfLowerTowerLiftsVanish.lean&line=142#L142)
-/
theorem _root_.GlobalTheory.T.thetaLifts_cuspidal_of_lower_tower_lifts_vanish : ∀ (D : D7) (X : ProvA), Inputs D X → LowAll D X → CuspAll D X := by
  first | exact @GlobalTheory.PairLift.cuspAll_of_lowAll | exact GlobalTheory.PairLift.cuspAll_of_lowAll | (intros; apply GlobalTheory.PairLift.cuspAll_of_lowAll <;> assumption)
