import Mathlib
import Formalism.ThetaSupremumBounds.StatementB

open Finset

namespace Formalism.DimensionVariation

/- English proof (translation)
Introduce `Cl Cl' _ _ A B _ _ _ _ γ γ' ε T tmax fn hγ hγ' hε hT`. Establish `key : ∀ L', ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2 ≤ (Fintype.card Cl : ℝ) * tmax * ∑ L, γ L * ‖fn L‖ ^ 2`. Introduce `L'`. Establish `h1 : ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ≤ ∑ L, γ L * (‖T L L'‖ * ‖fn L‖)`. Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun L _ => ?_)` and prove the remaining obligations.

Rewrite using `[norm_smul, norm_mul, hε, mul_one, Complex.norm_real, Real.norm_of_nonneg (hγ L).1.le]`. Conclude with `mul_le_mul_of_nonneg_left ((T L L').le_opNorm _) (hγ L).1.le`. Establish `h2 : (∑ L, γ L * (‖T L L'‖ * ‖fn L‖)) ^ 2 ≤ (∑ L, γ L * ‖T L L'‖ ^ 2) * ∑ L, γ L * ‖fn L‖ ^ 2`. Establish `hs` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun L => Real.sqrt (γ L) * ‖T L L'‖) (fun L => Real.sqrt (γ L) * ‖fn L‖)`. Establish `e1 : ∀ L, Real.sqrt (γ L) * ‖T L L'‖ * (Real.sqrt (γ L) * ‖fn L‖) = γ L * (‖T L L'‖ * ‖fn L‖)`.

Introduce `L`. Use `Real.mul_self_sqrt (hγ L).1.le` as an intermediate fact. Combine the equalities or inequalities in the displayed calculation. Establish `e2 : ∀ (L) (x : ℝ), (Real.sqrt (γ L) * x) ^ 2 = γ L * x ^ 2`. Introduce `L x`.

Rewrite using `[mul_pow, Real.sq_sqrt (hγ L).1.le]`. Simplify using `only [e1, e2] at hs`. Conclude with `hs`. Establish `h3 : ∑ L, γ L * ‖T L L'‖ ^ 2 ≤ (Fintype.card Cl : ℝ) * tmax`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun L _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by simp [Finset.sum_const, Finset.card_univ]`. Establish `hf : 0 ≤ ∑ L, γ L * ‖fn L‖ ^ 2` using `Finset.sum_nonneg fun L _ => mul_nonneg (hγ L).1.le (sq_nonneg _)`. Combine the equalities or inequalities in the displayed calculation.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun L' _ => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `_ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring`.
-/
theorem weightedSchurBound : ClassSchur := by
  intro Cl Cl' _ _ A B _ _ _ _ γ γ' ε T tmax fn hγ hγ' hε hT

  have key : ∀ L', ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2 ≤
      (Fintype.card Cl : ℝ) * tmax * ∑ L, γ L * ‖fn L‖ ^ 2 := by
    intro L'
    have h1 : ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ≤
        ∑ L, γ L * (‖T L L'‖ * ‖fn L‖) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun L _ => ?_)
      rw [norm_smul, norm_mul, hε, mul_one, Complex.norm_real, Real.norm_of_nonneg (hγ L).1.le]
      exact mul_le_mul_of_nonneg_left ((T L L').le_opNorm _) (hγ L).1.le
    have h2 : (∑ L, γ L * (‖T L L'‖ * ‖fn L‖)) ^ 2 ≤
        (∑ L, γ L * ‖T L L'‖ ^ 2) * ∑ L, γ L * ‖fn L‖ ^ 2 := by
      have hs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
        (fun L => Real.sqrt (γ L) * ‖T L L'‖) (fun L => Real.sqrt (γ L) * ‖fn L‖)
      have e1 : ∀ L, Real.sqrt (γ L) * ‖T L L'‖ * (Real.sqrt (γ L) * ‖fn L‖) =
          γ L * (‖T L L'‖ * ‖fn L‖) := by
        intro L
        have := Real.mul_self_sqrt (hγ L).1.le
        calc _ = (Real.sqrt (γ L) * Real.sqrt (γ L)) * (‖T L L'‖ * ‖fn L‖) := by ring
          _ = _ := by rw [this]
      have e2 : ∀ (L) (x : ℝ), (Real.sqrt (γ L) * x) ^ 2 = γ L * x ^ 2 := by
        intro L x
        rw [mul_pow, Real.sq_sqrt (hγ L).1.le]
      simp only [e1, e2] at hs
      exact hs
    have h3 : ∑ L, γ L * ‖T L L'‖ ^ 2 ≤ (Fintype.card Cl : ℝ) * tmax := by
      calc ∑ L, γ L * ‖T L L'‖ ^ 2 ≤ ∑ _L : Cl, tmax := by
            refine Finset.sum_le_sum fun L _ => ?_
            calc γ L * ‖T L L'‖ ^ 2 ≤ 1 * ‖T L L'‖ ^ 2 :=
                  mul_le_mul_of_nonneg_right (hγ L).2 (sq_nonneg _)
              _ ≤ tmax := by rw [one_mul]; exact hT L L'
        _ = _ := by simp [Finset.sum_const, Finset.card_univ]
    have hf : 0 ≤ ∑ L, γ L * ‖fn L‖ ^ 2 :=
      Finset.sum_nonneg fun L _ => mul_nonneg (hγ L).1.le (sq_nonneg _)
    calc ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2
        ≤ (∑ L, γ L * (‖T L L'‖ * ‖fn L‖)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hf
  calc (∑ L', γ' L' * ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2)
      ≤ ∑ _L' : Cl', (Fintype.card Cl : ℝ) * tmax * ∑ L, γ L * ‖fn L‖ ^ 2 := by
        refine Finset.sum_le_sum fun L' _ => ?_
        calc γ' L' * ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2
            ≤ 1 * ‖∑ L, ((γ L : ℂ) * ε L L') • T L L' (fn L)‖ ^ 2 :=
              mul_le_mul_of_nonneg_right (hγ' L').2 (sq_nonneg _)
          _ ≤ _ := by rw [one_mul]; exact key L'
    _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring

end Formalism.DimensionVariation
