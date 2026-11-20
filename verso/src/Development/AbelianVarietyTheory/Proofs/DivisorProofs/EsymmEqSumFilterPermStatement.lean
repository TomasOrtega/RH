import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmEqSumFilterPerm
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.JSW.esymm_mul_alternant` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEsymmEqSumFilterPerm.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.esymm_mul_det_pow_eq_sum_det_shifted : ∀ (n : ℕ) (m : Fin n → ℕ) (j : ℕ), MvPolynomial.esymm (Fin n) ℤ j * Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ m k) = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j), Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (m k + if k ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_alternant | exact GlobalTheory.JSW.esymm_mul_alternant | (intros; apply GlobalTheory.JSW.esymm_mul_alternant <;> assumption)
