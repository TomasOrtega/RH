import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexConjEqOfPowEq
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.relIndex_conj_eq_of_pow_eq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRelIndexConjEqOfPowEq.lean&line=104#L104)
-/
theorem _root_.GlobalTheory.T.relIndex_map_conj_symm_of_relIndex_map_conj_pow_symm : ∀ (A : Type) [Group A] (K : Subgroup A) (g : A) (n : ℕ), 0 < n → (K.map (MulAut.conj g).toMonoidHom).relIndex K ≠ 0 → K.relIndex (K.map (MulAut.conj g).toMonoidHom) ≠ 0 → (K.map (MulAut.conj (g ^ n)).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj (g ^ n)).toMonoidHom) → (K.map (MulAut.conj g).toMonoidHom).relIndex K = K.relIndex (K.map (MulAut.conj g).toMonoidHom) := by
  first | exact @GlobalTheory.relIndex_conj_eq_of_pow_eq | exact GlobalTheory.relIndex_conj_eq_of_pow_eq | (intros; apply GlobalTheory.relIndex_conj_eq_of_pow_eq <;> assumption)
