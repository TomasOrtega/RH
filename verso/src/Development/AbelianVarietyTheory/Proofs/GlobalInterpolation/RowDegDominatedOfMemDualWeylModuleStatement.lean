import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowDegDominatedOfMemDualWeylModule
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FRowDegDominatedOfMemDualWeylModule.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.rowDeg_dominated_of_mem_dualWeylModule : ∀ (k : Type) [Field k] (N : ℕ) (ν : Fin N → ℕ), ∀ f ∈ dualWeyl k N N ν, ∀ m ∈ f.support, (∀ j : ℕ, (∑ a : Fin N with a.val < j, rowDeg m a) ≤ ∑ a : Fin N with a.val < j, ν a) ∧ ∑ a, rowDeg m a = ∑ a, ν a := by
  first | exact @GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl | exact GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl | (intros; apply GlobalTheory.Alc.rowDeg_dominated_of_mem_dualWeyl <;> assumption)
