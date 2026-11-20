import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsilonAlternatingSumZero
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsOfCZero
open MeasureTheory Finset GlobalTheory.Chamber
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Chamber.langlands_fourier_sum` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FEpsilonAlternatingSumZero.lean&line=51#L51)
-/
theorem _root_.GlobalTheory.T.epsilon_alternating_sum_zero : ∀ (k : ℕ) (P S : Finset (SV k)), IsPar P → S ⊆ P → S ≠ P → ∀ l ∈ generic k, ∑ R ∈ between P S, (-1 : ℂ) ^ (P \ R).card * epsHat P R l * eps R S l = 0 := by
  first | exact @GlobalTheory.Chamber.langlands_fourier_sum | exact GlobalTheory.Chamber.langlands_fourier_sum | (intros; apply GlobalTheory.Chamber.langlands_fourier_sum <;> assumption)
