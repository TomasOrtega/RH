import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeSumProdNormLeOfProdNormLowerBound
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ProdNormSum.lattice_sum_le` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLatticeSumProdNormLeOfProdNormLowerBound.lean&line=225#L225)
-/
theorem _root_.GlobalTheory.T.lattice_sum_prod_norm_le_of_prod_norm_lower_bound : ∀ (ι : Type) [Fintype ι] [Nonempty ι] (n : ℕ) (Λ : AddSubgroup (ι → EuclideanSpace ℂ (Fin n))) (R : ℝ), 1 ≤ n → 1 < R → (∀ w ∈ Λ, w ≠ 0 → R ≤ ∏ τ, ‖w τ‖) → ∀ s : Finset (ι → EuclideanSpace ℂ (Fin n)), (∀ w ∈ s, w ∈ Λ ∧ w ≠ 0) → ∑ w ∈ s, ∏ τ, (((1 + ‖w τ‖) / 3) ^ (2 * n + 5))⁻¹ ≤ Real.exp ((6 * n + 9) * Fintype.card ι) / R := by
  first | exact @GlobalTheory.ProdNormSum.lattice_sum_le | exact GlobalTheory.ProdNormSum.lattice_sum_le | (intros; apply GlobalTheory.ProdNormSum.lattice_sum_le <;> assumption)
