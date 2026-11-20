import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelCoinvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.KCoinvGood.kCoinv | exact GlobalTheory.KCoinvGood.kCoinv | (intros; apply GlobalTheory.KCoinvGood.kCoinv <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.theta_kernel_coinvariant : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.KCoinv := by
  first | exact @GlobalTheory.KCoinvGood.kCoinv | exact GlobalTheory.KCoinvGood.kCoinv | (intros; apply GlobalTheory.KCoinvGood.kCoinv <;> assumption)
