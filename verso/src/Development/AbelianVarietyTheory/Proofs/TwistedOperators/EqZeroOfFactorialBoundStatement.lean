import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFactorialBound
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SameBlockOfPosC
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FactorialJet.eq_zero_of_factorial_bound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FEqZeroOfFactorialBound.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_factorial_bound_of_vanish_at_zero : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (g : ℕ → ℝ → E) (C ρ : ℝ), 0 ≤ C → 0 < ρ → (∀ k t, HasDerivAt (g k) (g (k + 1) t) t) → (∀ k t, ‖g k t‖ ≤ C * ρ ^ k * (k.factorial : ℝ)) → (∀ k, g k 0 = 0) → ∀ k t, g k t = 0 := by
  first | exact @GlobalTheory.FactorialJet.eq_zero_of_factorial_bound | exact GlobalTheory.FactorialJet.eq_zero_of_factorial_bound | (intros; apply GlobalTheory.FactorialJet.eq_zero_of_factorial_bound <;> assumption)
