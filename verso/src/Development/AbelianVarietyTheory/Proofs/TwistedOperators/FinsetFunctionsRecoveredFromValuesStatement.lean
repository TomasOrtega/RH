import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinsetFunctionsRecoveredFromValues
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finset_functions_recovered_from_values` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FFinsetFunctionsRecoveredFromValues.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_finset_eq_sum_smul_of_mem_submodule : ∀ {X : Type} (V : Submodule ℂ (X → ℂ)) (F : Finset (X → ℂ)), (∀ u ∈ F, u ∈ V) →
    ∃ (s : Finset X) (E : X → X → ℂ), (∀ x, E x ∈ V) ∧ ∀ u ∈ F, u = ∑ x ∈ s, u x • E x := by
  first | exact @GlobalTheory.finset_functions_recovered_from_values | exact GlobalTheory.finset_functions_recovered_from_values | (intros; apply GlobalTheory.finset_functions_recovered_from_values <;> assumption)
