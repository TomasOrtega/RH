import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarCapelliTruncatedPerelomovPopov
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PosPartUnitaryMul
open Formalism.REAL Finset Polynomial
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ScalarNewton.scalar_newton` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FScalarCapelliTruncatedPerelomovPopov.lean&line=176#L176)
-/
theorem _root_.GlobalTheory.T.scalar_capelli_truncated_perelomov_popov : ∀ (m N : ℕ) (χ : Fin (m + 1) → ℂ), ∃ r : ℂ[X], r.natDegree ≤ m ∧ ∀ u : ℂ, (u - m) ^ (N + 1) * (∏ s, (u + 1 - (m : ℂ) / 2 + χ s) - ∏ s, (u - (m : ℂ) / 2 + χ s)) - (∏ s, (u - (m : ℂ) / 2 + χ s)) * ∑ k ∈ range (N + 1), (-1) ^ k * (u - m) ^ (N - k) * GlobalTheory.Dec.gelfVal χ k = r.eval u := by
  first | exact @GlobalTheory.ScalarNewton.scalar_newton | exact GlobalTheory.ScalarNewton.scalar_newton | (intros; apply GlobalTheory.ScalarNewton.scalar_newton <;> assumption)
