import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteCoeffTendstoAndBoundedStatement
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Use the polynomial consequences of the given equalities and inequalities.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts.

Rewrite the conclusion using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Use linear arithmetic over natural numbers and integers.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem tendsto_finCoeff_sum_jacobiTheta₂ : ∀ (τ : ℂ) (z : ℂ), 0 < τ.im →
    Filter.Tendsto (fun n : ℕ => ∑ j ∈ Finset.Icc (-(n : ℤ)) n,
      GlobalTheory.JacobiTriple.finCoeff (cexp (π * I * τ) ^ 2) n j * jacobiTheta₂_term j z τ)
      Filter.atTop (nhds (jacobiTheta₂ z τ * (GlobalTheory.JacobiTriple.qPochInf (cexp (π * I * τ) ^ 2))⁻¹)) := by
  intro τ z hτ
  set t := cexp (π * I * τ) ^ 2 with ht
  have hs : ‖cexp (π * I * τ)‖ < 1 := norm_exp_pi_I_lt_one τ hτ
  have ht1 : ‖t‖ < 1 := by
    rw [ht, norm_pow]
    nlinarith [norm_nonneg (cexp (π * I * τ))]
  obtain ⟨hlim, C, hC⟩ := GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded t ht1
  have hsum : Summable (fun j : ℤ => C * ‖jacobiTheta₂_term j z τ‖) :=
    ((summable_jacobiTheta₂_term_iff z τ).2 hτ).norm.mul_left C
  have hT := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (n : ℕ) (j : ℤ) => finCoeff t n j * jacobiTheta₂_term j z τ)
    (g := fun j => jacobiTheta₂_term j z τ * (qPochInf t)⁻¹) hsum
    (fun j => by
      have := (hlim j).mul_const (jacobiTheta₂_term j z τ)
      simpa [mul_comm] using this)
    (Filter.Eventually.of_forall fun n j => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right (hC n j) (norm_nonneg _))
  rw [tsum_mul_right] at hT
  refine hT.congr (fun n => ?_)
  apply tsum_eq_sum
  intro j hj
  have : ¬ j.natAbs ≤ n := by
    intro h
    apply hj
    rw [Finset.mem_Icc]
    omega
  simp [finCoeff, this]

end GlobalTheory.JacobiTriple
