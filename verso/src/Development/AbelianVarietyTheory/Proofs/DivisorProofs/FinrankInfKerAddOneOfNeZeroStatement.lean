import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankInfKerAddOneOfNeZero
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.finrank_inf_ker_add_one_of_ne_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFinrankInfKerAddOneOfNeZero.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.finrank_inf_ker_add_one_of_exists_ne_zero : ∀ (K : Type) [Field K] (r : ℕ) (V : Submodule K (Fin r → K)) (f : (Fin r → K) →ₗ[K] K), (∃ v ∈ V, f v ≠ 0) → Module.finrank K (V ⊓ LinearMap.ker f : Submodule K (Fin r → K)) + 1 = Module.finrank K V := by
  first | exact @GlobalTheory.finrank_inf_ker_add_one_of_ne_zero | exact GlobalTheory.finrank_inf_ker_add_one_of_ne_zero | (intros; apply GlobalTheory.finrank_inf_ker_add_one_of_ne_zero <;> assumption)
