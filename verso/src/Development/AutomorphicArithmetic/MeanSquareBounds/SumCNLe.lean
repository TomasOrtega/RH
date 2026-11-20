import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.TailMertens

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Take `⟨C, hC, hM⟩` from `Formalism.HermitianLattices.Ext.BoxTail.tail_mertens`. Use `⟨C + 1, by linarith, fun y Z hy hZ => ?_⟩` and prove the remaining obligations. Establish `hlog : 0 ≤ Real.log Z` using `Real.log_nonneg (by linarith)`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `n hn`. Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast (Finset.mem_Icc.mp hn).1`. Establish `hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n` using `ArithmeticFunction.vonMangoldt_nonneg`. Simplify using `only [cN]`. Combine the equalities or inequalities in the displayed calculation.

Use `_ = y * ∑ n ∈ Icc 1 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by`. Rewrite using `[Finset.mul_sum]`. Use `_ ≤ y * (C * Real.log Z) := mul_le_mul_of_nonneg_left (hM Z hZ) hy`. Use `_ ≤ (C + 1) * y * Real.log Z := by nlinarith [mul_nonneg hy hlog]`.
-/
theorem sum_cN_le :
    ∃ C : ℝ, 0 < C ∧ ∀ y Z : ℝ, 0 ≤ y → 2 ≤ Z → ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n ≤ C * y * Real.log Z := by
  obtain ⟨C, hC, hM⟩ := Formalism.HermitianLattices.Ext.BoxTail.tail_mertens
  refine ⟨C + 1, by linarith, fun y Z hy hZ => ?_⟩
  have hlog : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  calc ∑ n ∈ Icc 1 ⌊Z⌋₊, cN y n
        ≤ ∑ n ∈ Icc 1 ⌊Z⌋₊, y * (ArithmeticFunction.vonMangoldt n / (n : ℝ)) := by
          apply Finset.sum_le_sum
          intro n hn
          have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
          have hΛ : 0 ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
          simp only [cN]
          calc ArithmeticFunction.vonMangoldt n * min 1 (y / n)
              ≤ ArithmeticFunction.vonMangoldt n * (y / n) :=
                mul_le_mul_of_nonneg_left (min_le_right _ _) hΛ
            _ = y * (ArithmeticFunction.vonMangoldt n / n) := by ring
    _ = y * ∑ n ∈ Icc 1 ⌊Z⌋₊, ArithmeticFunction.vonMangoldt n / (n : ℝ) := by
          rw [Finset.mul_sum]
    _ ≤ y * (C * Real.log Z) := mul_le_mul_of_nonneg_left (hM Z hZ) hy
    _ ≤ (C + 1) * y * Real.log Z := by nlinarith [mul_nonneg hy hlog]

end QH
