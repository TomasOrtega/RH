import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerGeneratorApproxCriticalRadius
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKummerGeneratorApproxCriticalRadius.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.kummer_generator_approx_critical_radius : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (p : ℕ), p.Prime → ∀ F : Subfield L, ApproxRoot p v F → v (p : L) < 1 → ∀ α : L, α ^ p ∈ F → 0 < v (p : L) → ∀ s : ℝ≥0, 1 < s → ∃ y ∈ F, v (α - y) ^ (p - 1) ≤ s * v (p : L) * v α ^ (p - 1) := by
  first | exact @GlobalTheory.AlmostEt.kummer_approx_critical | exact GlobalTheory.AlmostEt.kummer_approx_critical | (intros; apply GlobalTheory.AlmostEt.kummer_approx_critical <;> assumption)
