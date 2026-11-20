import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsRealThetaParameterPairThetaPartnerSignedParame
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PairLift.FromSigned.thetaPar_partner` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FIsRealThetaParameterPairThetaPartnerSignedParame.lean&line=135#L135)
-/
theorem _root_.GlobalTheory.T.isRealThetaParameterPair_thetaPartnerSignedParameter : ∀ (t : ℕ) (b : Bool) (c c' : ℚ) (P : SPar) (N : ℕ), 1 ≤ t → P.Nonempty → GlobalTheory.SignedHC.IsRegular P → GlobalTheory.SignedHC.InCoset (c + ((t : ℚ) + 1) / 2) (GlobalTheory.SignedHC.entries P) → GlobalTheory.SignedHC.FarFrom c (((t : ℚ) + 1) / 2) P → P.card + t ≤ N → 1800 < N → GapOver P (2 * (N : ℚ) ^ 3) → GapOver (partner t b c c' P) (2 * (N : ℚ) ^ 3) → ThetaPar t P (partner t b c c' P) c c' := by
  first | exact @GlobalTheory.PairLift.FromSigned.thetaPar_partner | exact GlobalTheory.PairLift.FromSigned.thetaPar_partner | (intros; apply GlobalTheory.PairLift.FromSigned.thetaPar_partner <;> assumption)
