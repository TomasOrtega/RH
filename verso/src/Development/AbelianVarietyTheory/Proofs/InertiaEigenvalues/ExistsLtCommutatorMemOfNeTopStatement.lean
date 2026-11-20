import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLtCommutatorMemOfNeTop
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
open GlobalTheory.BI GlobalTheory.BrauerZero
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsLtCommutatorMemOfNeTop.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole : ∀ {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G), K ≠ ⊤ → ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K := by
  first | exact @GlobalTheory.exists_lt_commutator_mem_of_ne_top | exact GlobalTheory.exists_lt_commutator_mem_of_ne_top | (intros; apply GlobalTheory.exists_lt_commutator_mem_of_ne_top <;> assumption)
