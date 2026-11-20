import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MultipliableTpFactor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JacobiTripleFiniteCoeffTendstoAndBoundedStatement
open Complex
open scoped Real

namespace GlobalTheory.JacobiTriple

/- English proof (translation)
Introduce `τ z hτ`. Use `set t := cexp (π * I * τ) ^ 2 with ht`. Establish `hs : ‖cexp (π * I * τ)‖ < 1` using `norm_exp_pi_I_lt_one τ hτ`. Establish `ht1 : ‖t‖ < 1`. Rewrite using `[ht, norm_pow]`.

Use polynomial arithmetic with `[norm_nonneg (cexp (π * I * τ))]`. Take `⟨hlim, C, hC⟩` from `GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded t ht1`. Establish `hsum : Summable (fun j : ℤ => C * ‖jacobiTheta₂_term j z τ‖)` using `((summable_jacobiTheta₂_term_iff z τ).2 hτ).norm.mul_left C`. Establish `hT` using `tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop) (f := fun (n : ℕ) (j : ℤ) => finCoeff t n j * jacobiTheta₂_term j z τ) (g := fun j => jacobiTheta₂_term j z τ * (qPochInf t)⁻¹) hsum (fun j => by`. Use `(hlim j).mul_const (jacobiTheta₂_term j z τ)` as an intermediate fact.

Simplify `this)` using `[mul_comm]`. Use the proof step `(Filter.Eventually.of_forall fun n j => by`. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_right (hC n j) (norm_nonneg _))`. Rewrite `hT` using `[tsum_mul_right]`.

Use `hT.congr (fun n => ?_)` and prove the remaining obligations. Apply `tsum_eq_sum` to reduce the goal to its premises. Introduce `j hj`. Establish `: ¬ j.natAbs ≤ n`. Introduce `h`.

Apply `hj` to reduce the goal to its premises. Rewrite using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Simplify using `[finCoeff, this]`.
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
