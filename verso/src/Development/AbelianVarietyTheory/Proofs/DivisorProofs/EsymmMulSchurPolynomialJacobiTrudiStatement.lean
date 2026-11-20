import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudi
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEsymmMulSchurPolynomialJacobiTrudi.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.esymm_mul_schurPolynomialJacobiTrudi : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  first | exact @GlobalTheory.JSW.esymm_mul_schur | exact GlobalTheory.JSW.esymm_mul_schur | (intros; apply GlobalTheory.JSW.esymm_mul_schur <;> assumption)
