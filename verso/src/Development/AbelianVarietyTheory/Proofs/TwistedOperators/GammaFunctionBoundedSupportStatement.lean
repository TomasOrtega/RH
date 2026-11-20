import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GammaFunctionBoundedSupport
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Chamber.gamP_bounded_support` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FGammaFunctionBoundedSupport.lean&line=83#L83)
-/
theorem _root_.GlobalTheory.T.gamma_function_bounded_support : ∀ (k : ℕ) (P R : Finset (SV k)) (Y : A0 k), IsPar P → R ⊆ P → ∃ C : ℝ, ∀ H ∈ aMQ (aP P) R, gamP P R Y H ≠ 0 → ‖H‖ ≤ C := by
  first | exact @GlobalTheory.Chamber.gamP_bounded_support | exact GlobalTheory.Chamber.gamP_bounded_support | (intros; apply GlobalTheory.Chamber.gamP_bounded_support <;> assumption)
