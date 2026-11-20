import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedCountFiniteIndexSubgroups
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_card_subgroups_containing_nsmul_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBoundedCountFiniteIndexSubgroups.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.bounded_count_finite_index_subgroups : ∀ (A : Type) [AddCommGroup A] [Module.Finite ℤ A], ∃ c : ℕ, ∀ M : ℕ, 0 < M →
    ∃ T : Finset (AddSubgroup A), T.card ≤ M ^ c ∧ ∀ H : AddSubgroup A, (∀ x : A, M • x ∈ H) → H ∈ T := by
  first | exact @GlobalTheory.exists_card_subgroups_containing_nsmul_le | exact GlobalTheory.exists_card_subgroups_containing_nsmul_le | (intros; apply GlobalTheory.exists_card_subgroups_containing_nsmul_le <;> assumption)
