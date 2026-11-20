import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Introduce `y`. Establish `hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1) = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Icc]`.

Establish `hn1 : (1 : ℝ) ≤ n` using `by exact_mod_cast hn.1`. Establish `hy : (n : ℝ) ≤ y`. Establish `hk : 0 < ⌊y⌋₊` using `lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)`. Establish `hy0 : 0 ≤ y`. Assume the negation of the conclusion as `hneg`.

Use `push_neg at hneg`. Rewrite `hk` using `[Nat.floor_eq_zero.2 (lt_trans hneg zero_lt_one)]`. Conclude with `lt_irrefl 0 hk`. Conclude with `le_trans (by exact_mod_cast hn.2) (Nat.floor_le hy0)`. Establish `hpos : (0 : ℝ) < n` using `by linarith`.

Establish `: 0 ≤ y / (n : ℝ) - 1`. Rewrite using `[sub_nonneg, le_div_iff₀ hpos, one_mul]`. Conclude with `hy`. Rewrite using `[max_eq_left this]`. Establish `hre : (Deduction.ramp (fun _ => 1) y).re = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0`.

Establish `hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1)`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_Icc]`. Rewrite using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[Finset.sum_subset hsub]`. Simplify using `[Deduction.ramp, Complex.re_sum]`. Introduce `n hn hn'`. Establish `h0 : n = 0`. Rewrite `hn` using `[Finset.mem_range]`.

Rewrite `hn'` using `[Finset.mem_Icc]`. Use linear arithmetic over natural numbers and integers. Substitute `h0` using the available equality. Simplify using the standard rewrite rules. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [Formalism.Gz, Formalism.Sz, An.G]`. Rewrite using `[hsum]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [An.G, Deduction.G]`. Rewrite using `[hre]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.Comparison₂.Gz_eq :
    ∀ y : ℝ, Formalism.Gz y = An.G y ∧ An.G y = Deduction.G y := by
  intro y
  have hsum : ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n * (y / (n : ℝ) - 1)
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn.1
    have hy : (n : ℝ) ≤ y := by
      have hk : 0 < ⌊y⌋₊ := lt_of_lt_of_le Nat.zero_lt_one (le_trans hn.1 hn.2)
      have hy0 : 0 ≤ y := by
        by_contra hneg
        push_neg at hneg
        rw [Nat.floor_eq_zero.2 (lt_trans hneg zero_lt_one)] at hk
        exact lt_irrefl 0 hk
      exact le_trans (by exact_mod_cast hn.2) (Nat.floor_le hy0)
    have hpos : (0 : ℝ) < n := by linarith
    have : 0 ≤ y / (n : ℝ) - 1 := by
      rw [sub_nonneg, le_div_iff₀ hpos, one_mul]
      exact hy
    rw [max_eq_left this]
  have hre : (Deduction.ramp (fun _ => 1) y).re
      = ∑ n ∈ Finset.Icc 1 ⌊y⌋₊, An.abelian₂ n * max (y / (n : ℝ) - 1) 0 := by
    have hsub : Finset.Icc 1 ⌊y⌋₊ ⊆ Finset.range (⌊y⌋₊ + 1) := by
      intro n hn
      rw [Finset.mem_Icc] at hn
      rw [Finset.mem_range]
      omega
    rw [Finset.sum_subset hsub]
    · simp [Deduction.ramp, Complex.re_sum]
    · intro n hn hn'
      have h0 : n = 0 := by
        rw [Finset.mem_range] at hn
        rw [Finset.mem_Icc] at hn'
        omega
      subst h0
      simp
  refine ⟨?_, ?_⟩
  · simp only [Formalism.Gz, Formalism.Sz, An.G]
    rw [hsum]
    ring
  · simp only [An.G, Deduction.G]
    rw [hre]
    ring
