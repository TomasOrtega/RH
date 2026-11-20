import Formalism.LogSumExpBounds.NuclearBound

namespace Formalism.NuclearRankWeightBounds.P

open Finset Matrix

/- English proof (translation)
Use `set U : Matrix (Fin N) (Fin N) ℂ := (hY.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef`. Use `set D : Matrix (Fin N) (Fin N) ℂ := diagonal (RCLike.ofReal ∘ hY.eigenvalues) with hDdef`. Establish `hsp : Y = U * D * star U` using `by conv_lhs => rw [hY.spectral_theorem]`. Both sides reduce to the same expression. Establish `hu : star U * U = 1` using `Unitary.coe_star_mul_self hY.eigenvectorUnitary`.

Establish `h1 : (Y * Y).trace = (D * D).trace`. Establish `: Y * Y = U * (D * D) * star U`. Rewrite using `[hsp]`. Simplify using `only [mul_assoc]`. Rewrite using `[← mul_assoc (star U) U, hu, one_mul]`.

Rewrite using `[this, trace_mul_cycle, hu, one_mul]`. Establish `h2 : (D * D).trace = ∑ j, ((hY.eigenvalues j ^ 2 : ℝ) : ℂ)`. Rewrite using `[hDdef, diagonal_mul_diagonal, trace_diagonal]`. Simplify using `[pow_two]`. Establish `h3 : (Y * Y).trace = ∑ a, ∑ b, ((‖Y a b‖ ^ 2 : ℝ) : ℂ)` using `by conv_lhs => rw [show Y * Y = Yᴴ * Y by rw [hY.eq]]`.

Simplify using `only [trace, Matrix.diag, mul_apply, conjTranspose_apply]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[show star (Y a b) = (starRingEnd ℂ) (Y a b) from rfl, Complex.conj_mul']`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `h4 : ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ) = ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ)`. Simplify using `only [Complex.ofReal_sum]`. Rewrite using `[← h3, h1, h2]`. Conclude with `h4` after adjusting the coercions.
-/
theorem sum_sq_eigenvalues {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian) :
    ∑ j, hY.eigenvalues j ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 := by
  set U : Matrix (Fin N) (Fin N) ℂ := (hY.eigenvectorUnitary : Matrix (Fin N) (Fin N) ℂ) with hUdef
  set D : Matrix (Fin N) (Fin N) ℂ := diagonal (RCLike.ofReal ∘ hY.eigenvalues) with hDdef
  have hsp : Y = U * D * star U := by
    conv_lhs => rw [hY.spectral_theorem]
    rfl
  have hu : star U * U = 1 := Unitary.coe_star_mul_self hY.eigenvectorUnitary
  have h1 : (Y * Y).trace = (D * D).trace := by
    have : Y * Y = U * (D * D) * star U := by
      rw [hsp]
      simp only [mul_assoc]
      rw [← mul_assoc (star U) U, hu, one_mul]
    rw [this, trace_mul_cycle, hu, one_mul]
  have h2 : (D * D).trace = ∑ j, ((hY.eigenvalues j ^ 2 : ℝ) : ℂ) := by
    rw [hDdef, diagonal_mul_diagonal, trace_diagonal]
    simp [pow_two]
  have h3 : (Y * Y).trace = ∑ a, ∑ b, ((‖Y a b‖ ^ 2 : ℝ) : ℂ) := by
    conv_lhs => rw [show Y * Y = Yᴴ * Y by rw [hY.eq]]
    simp only [trace, Matrix.diag, mul_apply, conjTranspose_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [show star (Y a b) = (starRingEnd ℂ) (Y a b) from rfl, Complex.conj_mul']
    push_cast; ring
  have h4 : ((∑ j, hY.eigenvalues j ^ 2 : ℝ) : ℂ) = ((∑ a, ∑ b, ‖Y a b‖ ^ 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_sum]
    rw [← h3, h1, h2]
  exact_mod_cast h4

/- English proof (translation)
Introduce `N Y hY`. Use `set μ := hY.eigenvalues`. Establish `hrank : (Y.rank : ℝ) = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) ^ 2`. Rewrite using `[hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]`. Simplify using `only [ite_pow, one_pow, ne_eq, zero_pow two_ne_zero]`.

Rewrite using `[Finset.sum_boole]`. Establish `hhs : Formalism.NuclearRankWeightBounds.D.hs Y = Real.sqrt (∑ j, |μ j| ^ 2)`. Unfold `Formalism.NuclearRankWeightBounds.D.hs`. Rewrite using `[← sum_sq_eigenvalues Y hY]`. Simplify using `only [sq_abs]`.

Both sides reduce to the same expression. Establish `hsum : ∑ j, |μ j| = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) * |μ j|`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases h : μ j = 0 <;> simp [h]`. Rewrite using `[hrank, hhs, hsum]`.

Conclude with `Real.sum_mul_le_sqrt_mul_sqrt _ _ _`.
-/
theorem nuclear_norm_bound_holds : Formalism.NuclearRankWeightBounds.D.NuclearBound := by
  intro N Y hY
  classical
  set μ := hY.eigenvalues
  have hrank : (Y.rank : ℝ) = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) ^ 2 := by
    rw [hY.rank_eq_card_non_zero_eigs, Fintype.card_subtype]
    simp only [ite_pow, one_pow, ne_eq, zero_pow two_ne_zero]
    rw [Finset.sum_boole]
  have hhs : Formalism.NuclearRankWeightBounds.D.hs Y = Real.sqrt (∑ j, |μ j| ^ 2) := by
    unfold Formalism.NuclearRankWeightBounds.D.hs
    rw [← sum_sq_eigenvalues Y hY]
    simp only [sq_abs]
    rfl
  have hsum : ∑ j, |μ j| = ∑ j, (if μ j ≠ 0 then (1 : ℝ) else 0) * |μ j| := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : μ j = 0 <;> simp [h]
  rw [hrank, hhs, hsum]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

end Formalism.NuclearRankWeightBounds.P
