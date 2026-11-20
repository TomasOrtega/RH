import Mathlib
open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `N j B S d v lrd Lv hrec hB hj hB3 hl hrecb hBeq hprime hv hd hsv hsl`. Establish `hN : (0 : ℝ) ≤ N` using `Nat.cast_nonneg _`. Establish `hlogB : 1 ≤ Real.log B`. Establish `h3 : (3 : ℝ) ≤ B` using `by exact_mod_cast hB3`. Establish `hexp : Real.exp 1 ≤ B`.

Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `Real.log_le_log (Real.exp_pos 1) hexp` as an intermediate fact. Rewrite `this` using `[Real.log_exp]`. Then use the resulting hypothesis. Establish `hsum : |∑ p ∈ S, d p| ≤ N * (3 * Real.log B + 1) + N * lrd`.

Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_sum` to reduce the goal to its premises. Introduce `p hp`. Establish `hdp` using `hd p hp`. Establish `e : ((N : ℝ) / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p = (N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p)` using `by ring`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = (N : ℝ) * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) + N * ∑ p ∈ S, v p * Real.log p := by`. Rewrite using `[Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]`. Use `_ ≤ N * (3 * Real.log B + 1) + N * lrd := by gcongr`. Establish `htot : |hB| ≤ |hrec| + |∑ p ∈ S, d p|`.

Rewrite using `[hBeq]`. Conclude with `abs_add_le _ _`. Use polynomial arithmetic with `[mul_nonneg hN (sub_nonneg.mpr hlogB), mul_nonneg hN hl, mul_nonneg hN (abs_nonneg Lv)]`.
-/
theorem hB_bound : ∀ (N j B : ℕ) (S : Finset ℕ) (d v : ℕ → ℝ) (lrd Lv hrec hB : ℝ), j ≤ N → 3 ≤ B → 0 ≤ lrd → |hrec| ≤ N * (3 / 2 * lrd + |Lv| / 2) → hB = hrec + ∑ p ∈ S, d p → (∀ p ∈ S, p.Prime) → (∀ p ∈ S, 0 ≤ v p) → (∀ p ∈ S, |d p| ≤ (N / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p) → ∑ p ∈ S, v p * Real.log p ≤ lrd → ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) ≤ 3 * Real.log B + 1 → |hB| ≤ 4 * N * (Real.log B + lrd + |Lv|) := by
  intro N j B S d v lrd Lv hrec hB hj hB3 hl hrecb hBeq hprime hv hd hsv hsl
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hlogB : 1 ≤ Real.log B := by
    have h3 : (3 : ℝ) ≤ B := by exact_mod_cast hB3
    have hexp : Real.exp 1 ≤ B := by
      have := Real.exp_one_lt_d9
      linarith
    have := Real.log_le_log (Real.exp_pos 1) hexp
    rwa [Real.log_exp] at this
  have hsum : |∑ p ∈ S, d p| ≤ N * (3 * Real.log B + 1) + N * lrd := by
    calc |∑ p ∈ S, d p| ≤ ∑ p ∈ S, |d p| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ p ∈ S, ((N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hdp := hd p hp
        have e : ((N : ℝ) / ((p : ℝ) - 1) + j * v p + ((N : ℝ) - j) * v p) * Real.log p =
            (N : ℝ) * (Real.log p / ((p : ℝ) - 1)) + N * (v p * Real.log p) := by ring
        linarith
      _ = (N : ℝ) * ∑ p ∈ S, Real.log p / ((p : ℝ) - 1) + N * ∑ p ∈ S, v p * Real.log p := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ N * (3 * Real.log B + 1) + N * lrd := by gcongr
  have htot : |hB| ≤ |hrec| + |∑ p ∈ S, d p| := by
    rw [hBeq]; exact abs_add_le _ _
  nlinarith [mul_nonneg hN (sub_nonneg.mpr hlogB), mul_nonneg hN hl, mul_nonneg hN (abs_nonneg Lv)]

end GlobalTheory.CompanionTheory.Ar.Flat
