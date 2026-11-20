import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosMulExtendIntLinearForm
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_pos_mul_extend_int_linearForm` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsPosMulExtendIntLinearForm.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.exists_pos_mul_extend_int_linearForm' : ∀ (F : Type) [AddCommGroup F] [Module.Free ℤ F] [Module.Finite ℤ F] (P : Submodule ℤ F) (f : P →ₗ[ℤ] ℤ), ∃ c : ℤ, 0 < c ∧ ∃ lam : F →ₗ[ℤ] ℤ, ∀ x : P, lam x = c * f x := by
  first | exact @GlobalTheory.exists_pos_mul_extend_int_linearForm | exact GlobalTheory.exists_pos_mul_extend_int_linearForm | (intros; apply GlobalTheory.exists_pos_mul_extend_int_linearForm <;> assumption)
