import Mathlib
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions

open Finset ArithmeticFunction

namespace GlobalTheory

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Rewrite using `[Finset.sum_Icc_succ_top (by omega)]`. Establish `hp : 0 ≤ r ^ (n + 1)` using `pow_nonneg h0 _`.

Establish `: r ^ (n + 1 + 1) = r ^ (n + 1) * r` using `pow_succ _ _`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem geom_Icc_one_le_two_mul_sub (r : ℝ) (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2) (N : ℕ) :
    ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r - 2 * r ^ (N + 1) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hp : 0 ≤ r ^ (n + 1) := pow_nonneg h0 _
    have : r ^ (n + 1 + 1) = r ^ (n + 1) * r := pow_succ _ _
    nlinarith

/- English proof (translation)
Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Establish `hlog : 0 ≤ Real.log p` using `Real.log_nonneg (by linarith)`. Establish `hr0 : (0 : ℝ) ≤ 1 / (p : ℝ)` using `by positivity`. Establish `hr1 : 1 / (p : ℝ) ≤ 1 / 2` using `one_div_le_one_div_of_le (by norm_num) hp2`.

Unfold `Formalism.HermitianLattices.GL2a2.sP`. Use `set N := ⌊x ^ (400 : ℝ)⌋₊`. Establish `hc : 0 ≤ x * Real.log p` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun i hi => ?_` and prove the remaining obligations.

Establish `hi1 : i ≠ 0`. Use `(Finset.mem_Icc.1 (Finset.mem_filter.1 hi).1).1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Unfold `Formalism.HermitianLattices.GL2PrimeSums.cn`. Rewrite using `[vonMangoldt_apply_pow hi1, vonMangoldt_apply_prime hp]`.

Combine the equalities or inequalities in the displayed calculation. Use `push_cast`. Rewrite using `[one_div_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ ∑ i ∈ Icc 1 N, x * Real.log p * (1 / (p : ℝ)) ^ i := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => by positivity)`.

Use `_ = x * Real.log p * ∑ i ∈ Icc 1 N, (1 / (p : ℝ)) ^ i := by rw [Finset.mul_sum]`. Use `_ ≤ x * Real.log p * (2 * (1 / (p : ℝ))) := by`. Use `mul_le_mul_of_nonneg_left ?_ hc` and prove the remaining obligations. Establish `h` using `geom_Icc_one_le_two_mul_sub _ hr0 hr1 N`. Establish `: 0 ≤ (1 / (p : ℝ)) ^ (N + 1)` using `pow_nonneg hr0 _`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `_ = 2 * x * Real.log p / p := by ring`.
-/
theorem primePowerSum_le_two_mul_log_div (x : ℝ) (hx : 0 < x) (p : ℕ) (hp : p.Prime) :
    Formalism.HermitianLattices.GL2a2.sP x p ≤ 2 * x * Real.log p / p := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hr0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hr1 : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp2
  unfold Formalism.HermitianLattices.GL2a2.sP
  set N := ⌊x ^ (400 : ℝ)⌋₊
  have hc : 0 ≤ x * Real.log p := by positivity
  calc ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), Formalism.HermitianLattices.GL2PrimeSums.cn x (p ^ i)
      ≤ ∑ i ∈ (Icc 1 N).filter (fun i => p ^ i ≤ N), x * Real.log p * (1 / (p : ℝ)) ^ i := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi1 : i ≠ 0 := by
          have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hi).1).1
          omega
        unfold Formalism.HermitianLattices.GL2PrimeSums.cn
        rw [vonMangoldt_apply_pow hi1, vonMangoldt_apply_prime hp]
        calc Real.log p * min 1 (x / ((p ^ i : ℕ) : ℝ))
            ≤ Real.log p * (x / ((p ^ i : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left (min_le_right _ _) hlog
          _ = x * Real.log p * (1 / (p : ℝ)) ^ i := by
              push_cast
              rw [one_div_pow]
              ring
    _ ≤ ∑ i ∈ Icc 1 N, x * Real.log p * (1 / (p : ℝ)) ^ i :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => by positivity)
    _ = x * Real.log p * ∑ i ∈ Icc 1 N, (1 / (p : ℝ)) ^ i := by rw [Finset.mul_sum]
    _ ≤ x * Real.log p * (2 * (1 / (p : ℝ))) := by
        refine mul_le_mul_of_nonneg_left ?_ hc
        have h := geom_Icc_one_le_two_mul_sub _ hr0 hr1 N
        have : 0 ≤ (1 / (p : ℝ)) ^ (N + 1) := pow_nonneg hr0 _
        linarith
    _ = 2 * x * Real.log p / p := by ring

/- English proof (translation)
Introduce `x hx p hp _` and use `primePowerSum_le_two_mul_log_div x hx p hp`.
-/
theorem large_prime_sum_bound : Formalism.HermitianLattices.GL2a2.SizeSpLarge :=
  fun x hx p hp _ => primePowerSum_le_two_mul_log_div x hx p hp

end GlobalTheory
