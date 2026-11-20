import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientThetaParamsRemoveBlockArrow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RemoveBlock.removeBlock_pairPar` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FContragredientThetaParamsRemoveBlockArrow.lean&line=406#L406)
-/
theorem _root_.GlobalTheory.T.contragredientThetaParams_removeBlockArrow : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (i j : ℕ) (τ : D.what₂.Tau), i ≤ D.R.m → ∀ hj : j < D.R.m, PairPar (parV D i j τ) (parV D i (j + 1) τ) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i j)) (att (-(D.hc τ).e ⟨j, hj⟩) (rkV D i (j + 1))) := by
  first | exact @GlobalTheory.RemoveBlock.removeBlock_pairPar | exact GlobalTheory.RemoveBlock.removeBlock_pairPar | (intros; apply GlobalTheory.RemoveBlock.removeBlock_pairPar <;> assumption)
