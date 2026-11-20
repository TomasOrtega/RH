import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailFinal
import Development.AutomorphicArithmetic.MeanSquareBounds.TailKExp

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Take `⟨C0, hC0, hM⟩` from `Formalism.HermitianLattices.Ext.BoxTail.tail_mertens`. Use `⟨400 * C0 + 1, by positivity, ?_⟩` and prove the remaining obligations. Introduce `ε hε hε1`. Take `⟨Y1, hY1⟩` from `tailK ε 1 hε hε1 le_rfl`. Use `⟨max Y1 3, ?_⟩` and prove the remaining obligations.

Introduce `Y hY Q N _ χ hQ1 hQ2 hG`. Establish `hYY1 : Y ≥ Y1` using `le_trans (le_max_left _ _) hY`. Establish `hY3 : (3 : ℝ) ≤ Y` using `le_trans (le_max_right _ _) hY`. Establish `hY0 : (0 : ℝ) < Y` using `by linarith`. Establish `hT` using `hY1 Y hYY1 Q N χ hQ1 hQ2 hG`.

Establish `e1 : (Y ^ (1 : ℝ)) ^ 400 = Y ^ (400 : ℕ)` using `by simp`. Rewrite `hT` using `[e1, Real.rpow_one]`. Use `set z : ℝ := Y ^ (400 : ℕ) with hz`. Establish `hlogY : 1 ≤ Real.log Y`. Rewrite using `[Real.le_log_iff_exp_le hY0]`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hz2 : (2 : ℝ) ≤ z`. Establish `: Y ≤ Y ^ (400 : ℕ)` using `le_self_pow₀ (by linarith) (by norm_num)`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `htail : ‖tailL χ z‖ ≤ 1`. Rewrite `hT` using `[norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY0]`. Establish `hYe : Y ^ ε ≤ Y`. Use `Real.rpow_le_rpow_of_exponent_le (x := Y) (by linarith) hε1` as an intermediate fact. Simplify using `using this`.

Establish `: Y * ‖tailL χ z‖ ≤ Y * 1` using `by linarith`. Conclude with `le_of_mul_le_mul_left this hY0`. Establish `hsum : ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ ≤ 400 * C0 * Real.log Y`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `n hn`. Rewrite using `[norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_natCast]`. Apply `div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)` to reduce the goal to its premises. Use `DirichletCharacter.norm_le_one χ (n : ZMod N)` as an intermediate fact. Establish `h0` using `(ArithmeticFunction.vonMangoldt_nonneg (n := n))`.

Use the polynomial consequences of the given equalities and inequalities. Use `_ ≤ C0 * Real.log z := hM z hz2`. Use `_ = 400 * C0 * Real.log Y := by rw [hz, Real.log_pow]; push_cast; ring`. Establish `hL : logDerivLAtOne χ = -tailL χ z - ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n`. Unfold `tailL`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hL]`. Combine the equalities or inequalities in the displayed calculation. Use `(norm_sub_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[norm_neg]`.

Use `_ ≤ 1 + 400 * C0 * Real.log Y := add_le_add htail hsum`. Use `_ ≤ (400 * C0 + 1) * Real.log Y := by nlinarith`.
-/
theorem kappaC :
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∃ Y₀ : ℝ, ∀ Y ≥ Y₀, ∀ (Q : ℝ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
      Y ^ (ε / 6) ≤ Real.log Q → Real.log Q ≤ Y ^ (ε / 4) → GoodC Q χ → ‖logDerivLAtOne χ‖ ≤ C * Real.log Y := by
  obtain ⟨C0, hC0, hM⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨400 * C0 + 1, by positivity, ?_⟩
  intro ε hε hε1
  obtain ⟨Y1, hY1⟩ := tailK ε 1 hε hε1 le_rfl
  refine ⟨max Y1 3, ?_⟩
  intro Y hY Q N _ χ hQ1 hQ2 hG
  have hYY1 : Y ≥ Y1 := le_trans (le_max_left _ _) hY
  have hY3 : (3 : ℝ) ≤ Y := le_trans (le_max_right _ _) hY
  have hY0 : (0 : ℝ) < Y := by linarith
  have hT := hY1 Y hYY1 Q N χ hQ1 hQ2 hG
  have e1 : (Y ^ (1 : ℝ)) ^ 400 = Y ^ (400 : ℕ) := by simp
  rw [e1, Real.rpow_one] at hT
  set z : ℝ := Y ^ (400 : ℕ) with hz
  have hlogY : 1 ≤ Real.log Y := by
    rw [Real.le_log_iff_exp_le hY0]
    have := Real.exp_one_lt_d9
    linarith
  have hz2 : (2 : ℝ) ≤ z := by
    have : Y ≤ Y ^ (400 : ℕ) := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  have htail : ‖tailL χ z‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hY0] at hT
    have hYe : Y ^ ε ≤ Y := by
      have := Real.rpow_le_rpow_of_exponent_le (x := Y) (by linarith) hε1
      simpa using this
    have : Y * ‖tailL χ z‖ ≤ Y * 1 := by linarith
    exact le_of_mul_le_mul_left this hY0
  have hsum : ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ ≤ 400 * C0 * Real.log Y := by
    calc ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖
        ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, ‖(ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ Icc 1 ⌊z⌋₊, ArithmeticFunction.vonMangoldt n / n := by
        apply Finset.sum_le_sum
        intro n hn
        rw [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg, Complex.norm_natCast]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        have := DirichletCharacter.norm_le_one χ (n : ZMod N)
        have h0 := (ArithmeticFunction.vonMangoldt_nonneg (n := n))
        nlinarith
      _ ≤ C0 * Real.log z := hM z hz2
      _ = 400 * C0 * Real.log Y := by rw [hz, Real.log_pow]; push_cast; ring
  have hL : logDerivLAtOne χ = -tailL χ z - ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n := by
    unfold tailL
    ring
  rw [hL]
  calc ‖-tailL χ z - ∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖
      ≤ ‖tailL χ z‖ + ‖∑ n ∈ Icc 1 ⌊z⌋₊, (ArithmeticFunction.vonMangoldt n : ℂ) * χ n / n‖ := by
        refine (norm_sub_le _ _).trans ?_
        rw [norm_neg]
    _ ≤ 1 + 400 * C0 * Real.log Y := add_le_add htail hsum
    _ ≤ (400 * C0 + 1) * Real.log Y := by nlinarith

end QH
