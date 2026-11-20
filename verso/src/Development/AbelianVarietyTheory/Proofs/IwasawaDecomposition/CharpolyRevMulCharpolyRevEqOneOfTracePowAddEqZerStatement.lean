import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZer
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FCharpolyRevMulCharpolyRevEqOneOfTracePowAddEqZer.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.charpolyRev_mul_eq_one_of_trace_pow_add_eq_zero : ∀ {K R : Type} [Field K] [CharZero K] [CommRing R] [Algebra K R] {p q : ℕ} (M : Matrix (Fin p) (Fin p) R) (N : Matrix (Fin q) (Fin q) R), (∀ k, 1 ≤ k → (M ^ k).trace + (N ^ k).trace = 0) → M.charpolyRev * N.charpolyRev = 1 := by
  first | exact @GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | exact GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero | (intros; apply GlobalTheory.charpolyRev_mul_charpolyRev_eq_one_of_trace_pow_add_eq_zero <;> assumption)
