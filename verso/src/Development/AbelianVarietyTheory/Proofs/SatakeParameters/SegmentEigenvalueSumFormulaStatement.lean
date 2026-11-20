import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SegmentEigenvalueSumFormula
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.longest_segment_unique_of_bounded_remainder` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FSegmentEigenvalueSumFormula.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.segment_eigenvalue_sum_formula : ∀ (q t : ℕ) (L : List (ℕ × Multiset ℂ)) (Rw : Multiset ℂ) (c : ℂ), 1 < q → 1 ≤ t → ‖c‖ = 1 → (∀ x ∈ Rw, ‖x‖ < (q : ℝ) ^ (((t : ℝ) - 1) / 2)) → (∀ e ∈ L, 1 ≤ e.1 ∧ e.2 ≠ 0 ∧ ∀ α ∈ e.2, ‖α‖ = 1) → (L.map fun e => ((List.range e.1).map fun k => e.2.map (· * (q : ℂ) ^ (((((e.1 : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ))).sum).sum = Rw + ((List.range t).map fun k => ({c * (q : ℂ) ^ (((((t : ℝ) - 1) / 2 - (k : ℝ) : ℝ)) : ℂ)} : Multiset ℂ)).sum → (∃ e ∈ L, t ≤ e.1) ∧ ∀ e ∈ L, t ≤ e.1 → e.1 = t ∧ e.2 = {c} := by
  first | exact @GlobalTheory.longest_segment_unique_of_bounded_remainder | exact GlobalTheory.longest_segment_unique_of_bounded_remainder | (intros; apply GlobalTheory.longest_segment_unique_of_bounded_remainder <;> assumption)
