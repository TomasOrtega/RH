import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeparatingFamilySumClosedUnderProd
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.sepFamily_prod` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSeparatingFamilySumClosedUnderProd.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.separating_family_sum_closed_under_prod : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L] (F : Subfield L) (ι : Type) (s : Finset ι) (x y : ι → L), (∀ j ∈ s, x j ∈ F ∧ y j ∈ F ∧ v (x j) ≤ 1 ∧ v (y j) ≤ 1) → ∃ (n : ℕ) (a b : Fin n → L), (∀ i, a i ∈ F ∧ b i ∈ F ∧ v (a i) ≤ 1 ∧ v (b i) ≤ 1) ∧ ∀ σ : G, ∑ i, a i * σ • b i = ∏ j ∈ s, (x j - σ • y j) := by
  first | exact @GlobalTheory.sepFamily_prod | exact GlobalTheory.sepFamily_prod | (intros; apply GlobalTheory.sepFamily_prod <;> assumption)
