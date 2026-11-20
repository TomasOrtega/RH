import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardPermPartitionPartsMulCentralizer
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BadShare.card_perm_partition_parts_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCardPermPartitionPartsMulCentralizer.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.card_perm_partition_parts_mul_centralizer : ∀ (N : ℕ) (μ : Multiset ℕ), (∀ d ∈ μ, 0 < d) → μ.sum = N → (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => σ.partition.parts = μ).card * ∏ d ∈ μ.toFinset, (d ^ μ.count d * (μ.count d).factorial) = N.factorial := by
  first | exact @GlobalTheory.BadShare.card_perm_partition_parts_mul | exact GlobalTheory.BadShare.card_perm_partition_parts_mul | (intros; apply GlobalTheory.BadShare.card_perm_partition_parts_mul <;> assumption)
