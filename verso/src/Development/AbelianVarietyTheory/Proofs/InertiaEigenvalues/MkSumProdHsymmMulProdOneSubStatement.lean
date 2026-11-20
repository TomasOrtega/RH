import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MkSumProdHsymmMulProdOneSub
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FMkSumProdHsymmMulProdOneSub.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.mk_sum_hsymm_mul_prod_one_sub_eq_one : ∀ {m n : ℕ} (α : Fin n → ℂ) (β : Fin m → ℂ) (T : ℂ),
    PowerSeries.mk (fun d => T ^ d * ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j)) *
      ∏ p : Fin n × Fin m, (1 - PowerSeries.C (α p.1 * β p.2 * T) * PowerSeries.X) = 1 := by
  first | exact @GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub | exact GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub | (intros; apply GlobalTheory.JSW.mk_sum_prod_hsymm_mul_prod_one_sub <;> assumption)
