import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.HeckeLower

namespace PI.Residue

open MeasureTheory intervalIntegral

/- English proof (translation)
Establish `hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (1 : ℝ) (1 + N))`. Introduce `x hx y hy hxy`. Conclude with `Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)`. Establish `h1` using `hanti.sum_le_integral`. Use `h1.trans ?_` and prove the remaining obligations.

Establish `h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + N)`. Rewrite using `[Set.uIcc_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]`. Introduce `h`. Combine the linear relations using `[h.1]`. Rewrite using `[integral_rpow (Or.inr ⟨by linarith, h0⟩)]`.

Establish `hpos : 0 < s - 1` using `by linarith`. Establish `hN : 0 ≤ ((1 : ℝ) + N) ^ (-s + 1)` using `by positivity`. Rewrite using `[Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, neg_sub]`. Rewrite using `[show -(s - 1) = -s + 1 by ring]`. Apply `div_le_div_of_nonneg_right _ hpos.le` to reduce the goal to its premises.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem sum_range_le (s : ℝ) (hs : 1 < s) (N : ℕ) :
    ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) ≤ 1 / (s - 1) := by
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (1 : ℝ) (1 + N)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  refine h1.trans ?_
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 : ℝ) (1 + N) := by
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])]
    intro h
    linarith [h.1]
  rw [integral_rpow (Or.inr ⟨by linarith, h0⟩)]
  have hpos : 0 < s - 1 := by linarith
  have hN : 0 ≤ ((1 : ℝ) + N) ^ (-s + 1) := by positivity
  rw [Real.one_rpow, show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, neg_sub]
  rw [show -(s - 1) = -s + 1 by ring]
  apply div_le_div_of_nonneg_right _ hpos.le
  linarith

/- English proof (translation)
Introduce `s hs`. Unfold `zetaR`. Establish `hpos : 0 < s - 1` using `by linarith`. Apply `Real.tsum_le_of_sum_range_le` to reduce the goal to its premises. Introduce `n`.

Check the signs of the components of the expression. Introduce `n`. Consider the cases of `n with`. Consider the case `zero`. Simplify using `only [Finset.range_zero, Finset.sum_empty]`.

Check the signs of the components of the expression. Consider the case `succ N`. Rewrite using `[Finset.sum_range_succ']`. Use `sum_range_le s hs N` as an intermediate fact. Establish `e : ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) + 1) ^ (-s) = ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s)`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[add_comm]`. Rewrite using `[e]`. Simplify using `only [Nat.cast_zero, zero_add, Real.one_rpow]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem zetaRLe : ZetaRLe := by
  intro s hs
  unfold zetaR
  have hpos : 0 < s - 1 := by linarith
  apply Real.tsum_le_of_sum_range_le
  · intro n
    positivity
  · intro n
    cases n with
    | zero =>
      simp only [Finset.range_zero, Finset.sum_empty]
      positivity
    | succ N =>
      rw [Finset.sum_range_succ']
      have := sum_range_le s hs N
      have e : ∑ i ∈ Finset.range N, (((i + 1 : ℕ) : ℝ) + 1) ^ (-s)
          = ∑ i ∈ Finset.range N, ((1 : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [add_comm]
      rw [e]
      simp only [Nat.cast_zero, zero_add, Real.one_rpow]
      linarith

end PI.Residue
