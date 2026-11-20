import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealThetaRuleExchangePairMembers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRealThetaRuleExchangePairMembers.lean&line=179#L179)
-/
theorem _root_.GlobalTheory.T.realThetaRule_exchange_pair_members : ∀ (X : ProvA) (p q r s : ℕ) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ), (Formalism.MainNotions.SchurIrreducible.ARiiiUp X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiDown X lam' lam) ∧ (Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam lam' → Formalism.MainNotions.SchurIrreducible.ARiiiLine X lam' lam) ∧ (Formalism.MainNotions.SchurIrreducible.ARiv X (r := r) (s := s) lam → NoLow X r s lam) := by
  first | exact @GlobalTheory.SwapRule.swap_rule | exact GlobalTheory.SwapRule.swap_rule | (intros; apply GlobalTheory.SwapRule.swap_rule <;> assumption)
