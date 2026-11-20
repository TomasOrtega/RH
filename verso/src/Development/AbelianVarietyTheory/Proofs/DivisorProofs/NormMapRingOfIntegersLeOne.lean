import Mathlib

namespace GlobalTheory.RingOfIntegersNormBound

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Take `⟨q, hq, hqx⟩` from `hx`. Rewrite `hqx` using `[Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ]`. Establish `hlead : q.coeff q.natDegree = 1` using `hq`.

Rewrite `hqx` using `[hlead, map_one, one_mul]`. Establish `hpow : x ^ q.natDegree = -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ F (q.coeff i) * x ^ i` using `eq_neg_of_add_eq_zero_right hqx`. Establish `hpos : 0 < ‖x‖` using `lt_trans one_pos hlt`. Establish `key : ∀ n : ℕ, ‖∑ i ∈ Finset.range n, algebraMap ℤ F (q.coeff i) * x ^ i‖ < ‖x‖ ^ n`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_range_succ]`. Establish `h1 : ‖x‖ ^ n < ‖x‖ ^ (n + 1)` using `pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)`.

Use `lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ih.trans h1) ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_pow]`. Establish `h2 : ‖algebraMap ℤ F (q.coeff n)‖ ≤ 1`. Simplify using `using IsUltrametricDist.norm_intCast_le_one F (q.coeff n)`. Combine the equalities or inequalities in the displayed calculation.

Use `key q.natDegree` as an intermediate fact. Rewrite `this` using `[← norm_neg, ← hpow, norm_pow]`. Conclude with `lt_irrefl _ this`.
-/
theorem norm_le_one_of_isIntegral {F : Type*} [NormedField F] [IsUltrametricDist F]
    {x : F} (hx : IsIntegral ℤ x) : ‖x‖ ≤ 1 := by
  by_contra hlt
  push_neg at hlt
  obtain ⟨q, hq, hqx⟩ := hx
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ] at hqx
  have hlead : q.coeff q.natDegree = 1 := hq
  rw [hlead, map_one, one_mul] at hqx
  have hpow : x ^ q.natDegree =
      -∑ i ∈ Finset.range q.natDegree, algebraMap ℤ F (q.coeff i) * x ^ i :=
    eq_neg_of_add_eq_zero_right hqx
  have hpos : 0 < ‖x‖ := lt_trans one_pos hlt
  have key : ∀ n : ℕ,
      ‖∑ i ∈ Finset.range n, algebraMap ℤ F (q.coeff i) * x ^ i‖ < ‖x‖ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]
      have h1 : ‖x‖ ^ n < ‖x‖ ^ (n + 1) := pow_lt_pow_right₀ hlt (Nat.lt_succ_self n)
      refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) (max_lt (ih.trans h1) ?_)
      rw [norm_mul, norm_pow]
      have h2 : ‖algebraMap ℤ F (q.coeff n)‖ ≤ 1 := by
        simpa using IsUltrametricDist.norm_intCast_le_one F (q.coeff n)
      calc ‖algebraMap ℤ F (q.coeff n)‖ * ‖x‖ ^ n ≤ 1 * ‖x‖ ^ n :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = ‖x‖ ^ n := one_mul _
        _ < _ := h1
  have := key q.natDegree
  rw [← norm_neg, ← hpow, norm_pow] at this
  exact lt_irrefl _ this

/- English proof (translation)
The claim follows from `norm_le_one_of_isIntegral (map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe c))`.
-/
theorem norm_map_ringOfIntegers_le_one {K : Type} [Field K] [NumberField K] {p : ℕ}
    [Fact (Nat.Prime p)] (f : K →+* ℂ_[p]) (c : NumberField.RingOfIntegers K) :
    ‖(f : K → ℂ_[p]) (↑c : K)‖ ≤ (1 : ℝ) :=
  norm_le_one_of_isIntegral (map_isIntegral_int f (NumberField.RingOfIntegers.isIntegral_coe c))

end GlobalTheory.RingOfIntegersNormBound
