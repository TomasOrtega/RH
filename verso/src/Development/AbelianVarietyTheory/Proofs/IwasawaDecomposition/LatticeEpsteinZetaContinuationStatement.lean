import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeEpsteinZetaContinuation
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
open Complex Filter Asymptotics
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FLatticeEpsteinZetaContinuation.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.lattice_epstein_zeta_continuation : ∀ (w₁ w₂ x₀ : ℂ), (starRingEnd ℂ w₁ * w₂).im ≠ 0 → (∀ m n : ℤ, x₀ + m * w₁ + n * w₂ ≠ 0) → ∃ Z : ℂ → ℂ, Differentiable ℂ Z ∧ Z 1 = (Real.pi / |(starRingEnd ℂ w₁ * w₂).im| : ℝ) ∧ Z (-1) = 0 ∧ ∀ s : ℂ, 1 < s.re → Summable (fun p : ℤ × ℤ => ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s)) ∧ Z s = (s - 1) * ∑' p : ℤ × ℤ, ((‖x₀ + p.1 * w₁ + p.2 * w₂‖ ^ 2 : ℝ) : ℂ) ^ (-s) := by
  first | exact @GlobalTheory.epsteinZeta_shifted_continuation | exact GlobalTheory.epsteinZeta_shifted_continuation | (intros; apply GlobalTheory.epsteinZeta_shifted_continuation <;> assumption)
