import Development.AutomorphicArithmetic.MeanSquareBounds.PrimeSetTwoBounds
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagA
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.JacobiCharacterSums.MSqDiagB

open Finset Formalism.HermitianLattices.ZeroFreeRegionGL2 Formalism.HermitianLattices.Ext.LogarithmicIntegralBounds

namespace QH

/- English proof (translation)
Establish `hp2 : 2 ≤ p` using `hp.two_le`. Establish `key : ∀ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), ∃ k ∈ Icc 1 N, p ^ k = n`. Introduce `n hn`. Rewrite `hn` using `[Finset.mem_filter, Finset.mem_Icc]`. Take `⟨⟨_, hnN⟩, hpp, hmin⟩` from `hn`.

Take `⟨q, k, hq, hk, rfl⟩` from `(isPrimePow_nat_iff _).1 hpp`. Rewrite `hmin` using `[hq.pow_minFac hk.ne']`. Substitute `hmin` using the available equality. Use `⟨k, Finset.mem_Icc.2 ⟨hk, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `((Nat.lt_pow_self (by omega : 1 < q)).le).trans hnN`.

Establish `hlogp : 0 ≤ Real.log p` using `Real.log_nonneg (by exact_mod_cast hp.one_lt.le)`. Unfold `sP`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun n hn => ?_` and prove the remaining obligations. Take `⟨k, hk, rfl⟩` from `key n hn`.

Establish `hk0 : k ≠ 0` using `by have := (Finset.mem_Icc.1 hk).1; omega`. Rewrite using `[cN, ArithmeticFunction.vonMangoldt_apply_pow hk0, ArithmeticFunction.vonMangoldt_apply_prime hp]`. Use `_ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * min 1 (x / (n : ℝ)) := by`. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_` and prove the remaining obligations. Introduce `n hn`.

Take `⟨k, hk, rfl⟩` from `key n hn`. Conclude with `Finset.mem_image.2 ⟨k, hk, rfl⟩`. Conclude with `mul_nonneg hlogp (le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg _)))`. Use `_ = ∑ k ∈ Icc 1 N, Real.log p * min 1 (x / (p : ℝ) ^ k) := by`. Rewrite using `[Finset.sum_image fun a _ b _ h => Nat.pow_right_injective hp2 h]`.

Use `push_cast`. Both sides reduce to the same expression. Use `_ = _ := (Finset.mul_sum _ _ _).symm`.
-/
private lemma primePowerSum_le_log_mul_sum_min {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    sP (cN x) N p ≤ Real.log p * ∑ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) := by
  have hp2 : 2 ≤ p := hp.two_le
  have key : ∀ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
      ∃ k ∈ Icc 1 N, p ^ k = n := by
    intro n hn
    rw [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨_, hnN⟩, hpp, hmin⟩ := hn
    obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff _).1 hpp
    rw [hq.pow_minFac hk.ne'] at hmin
    subst hmin
    refine ⟨k, Finset.mem_Icc.2 ⟨hk, ?_⟩, rfl⟩
    exact ((Nat.lt_pow_self (by omega : 1 < q)).le).trans hnN
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  unfold sP
  calc ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p), cN x n
      = ∑ n ∈ (Icc 1 N).filter (fun n => IsPrimePow n ∧ n.minFac = p),
          Real.log p * min 1 (x / (n : ℝ)) := by
        refine Finset.sum_congr rfl fun n hn => ?_
        obtain ⟨k, hk, rfl⟩ := key n hn
        have hk0 : k ≠ 0 := by have := (Finset.mem_Icc.1 hk).1; omega
        rw [cN, ArithmeticFunction.vonMangoldt_apply_pow hk0,
          ArithmeticFunction.vonMangoldt_apply_prime hp]
    _ ≤ ∑ n ∈ (Icc 1 N).image (fun k => p ^ k), Real.log p * min 1 (x / (n : ℝ)) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun n _ _ => ?_
        · intro n hn
          obtain ⟨k, hk, rfl⟩ := key n hn
          exact Finset.mem_image.2 ⟨k, hk, rfl⟩
        · exact mul_nonneg hlogp (le_min zero_le_one (div_nonneg hx0 (Nat.cast_nonneg _)))
    _ = ∑ k ∈ Icc 1 N, Real.log p * min 1 (x / (p : ℝ) ^ k) := by
        rw [Finset.sum_image fun a _ b _ h => Nat.pow_right_injective hp2 h]
        push_cast
        rfl
    _ = _ := (Finset.mul_sum _ _ _).symm

/- English proof (translation)
Establish `hp2 : (2 : ℝ) ≤ p` using `by exact_mod_cast hp.two_le`. Establish `hp0 : (0 : ℝ) < p` using `by linarith`. Use `set r : ℝ := 1 / p with hr`. Establish `hr0 : 0 ≤ r` using `by positivity`. Establish `hr2 : r ≤ 1 / 2` using `by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hp2`.

Establish `hterm : ∀ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) ≤ x * r ^ i`. Introduce `i _`. Use `(min_le_right _ _).trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[hr, one_div_pow, mul_one_div]`. Use `(Finset.sum_le_sum hterm).trans ?_` and prove the remaining obligations.

Rewrite using `[← Finset.mul_sum]`. Break down `Nat.eq_zero_or_pos N with rfl | hN` into its components or cases. Rewrite using `[Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, mul_zero]`. Check the signs of the components of the expression. Establish `h1` using `dA_tail_geo r hr0 hr2 1 N hN`.

Simplify using `only [pow_one] at h1`. Establish `hsplit : ∑ i ∈ Icc 1 N, r ^ i = r + ∑ i ∈ Ioc 1 N, r ^ i`. Rewrite using `[dA_Icc_one_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN]`. Simplify using the standard rewrite rules. Establish `hle : ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r`.

Rewrite using `[hsplit]`. Combine the linear relations using `[pow_nonneg hr0 N]`. Combine the equalities or inequalities in the displayed calculation.
-/
private lemma sum_min_le_div {x : ℝ} (hx0 : 0 ≤ x) (N : ℕ) {p : ℕ} (hp : p.Prime) :
    ∑ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) ≤ 2 * (x / p) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  set r : ℝ := 1 / p with hr
  have hr0 : 0 ≤ r := by positivity
  have hr2 : r ≤ 1 / 2 := by rw [hr]; exact one_div_le_one_div_of_le (by norm_num) hp2
  have hterm : ∀ i ∈ Icc 1 N, min 1 (x / (p : ℝ) ^ i) ≤ x * r ^ i := by
    intro i _
    refine (min_le_right _ _).trans (le_of_eq ?_)
    rw [hr, one_div_pow, mul_one_div]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rw [Finset.Icc_eq_empty (by norm_num), Finset.sum_empty, mul_zero]
    positivity
  · have h1 := dA_tail_geo r hr0 hr2 1 N hN
    simp only [pow_one] at h1
    have hsplit : ∑ i ∈ Icc 1 N, r ^ i = r + ∑ i ∈ Ioc 1 N, r ^ i := by
      rw [dA_Icc_one_eq_Ioc, ← Finset.sum_Ioc_consecutive _ (Nat.zero_le 1) hN]
      simp
    have hle : ∑ i ∈ Icc 1 N, r ^ i ≤ 2 * r := by
      rw [hsplit]
      linarith [pow_nonneg hr0 N]
    calc x * ∑ i ∈ Icc 1 N, r ^ i ≤ x * (2 * r) := mul_le_mul_of_nonneg_left hle hx0
      _ = 2 * (x / p) := by rw [hr]; ring

/- English proof (translation)
Use `⟨3, by norm_num, fun y hy N p => ?_⟩` and prove the remaining obligations. Establish `hy0 : 0 < y` using `by linarith`. Establish `hly : 0 ≤ Real.log y` using `Real.log_nonneg (by linarith)`. Distinguish the cases in `hp : p.Prime`. Establish `h1` using `primePowerSum_le_log_mul_sum_min hy0.le N hp`.

Establish `hp0 : (0 : ℝ) < p` using `by exact_mod_cast hp.pos`. Establish `hlogp : 0 ≤ Real.log p` using `Real.log_nonneg (by exact_mod_cast hp.one_lt.le)`. Break down `le_total (p : ℝ) y with hpy | hpy` into its components or cases. Establish `h2` using `dA_sum_min_pow y (by linarith) p hp.two_le N`. Establish `h3 : Real.log p ≤ Real.log y` using `Real.log_le_log hp0 hpy`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2` using `mul_le_mul_of_nonneg_left (sum_min_le_div hy0.le N hp) hlogp`. Establish `he : Real.exp 1 ≤ y` using `by linarith [Real.exp_one_lt_d9]`. Establish `h4 : Real.log p / p ≤ Real.log y / y` using `Real.log_div_self_antitoneOn he (le_trans he hpy) hpy`. Establish `h5 : Real.log p * (2 * (y / p)) ≤ 2 * Real.log y`.

Establish `e : Real.log p * (2 * (y / p)) = 2 * y * (Real.log p / p)` using `by ring`. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0 : sP (cN y) N p = 0`.

Unfold `sP`. Use `Finset.sum_eq_zero fun n hn => ?_` and prove the remaining obligations. Rewrite `hn` using `[Finset.mem_filter]`. Take `⟨_, hpp, hmin⟩` from `hn`. Conclude with `absurd (hmin ▸ Nat.minFac_prime hpp.ne_one) hp`.

Rewrite using `[h0]`. Check the signs of the components of the expression.
-/
theorem exists_primePowerSum_le_mul_log :
    ∃ C : ℝ, 0 < C ∧ ∀ y : ℝ, 3 ≤ y → ∀ N p : ℕ, sP (cN y) N p ≤ C * Real.log y := by
  refine ⟨3, by norm_num, fun y hy N p => ?_⟩
  have hy0 : 0 < y := by linarith
  have hly : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  by_cases hp : p.Prime
  · have h1 := primePowerSum_le_log_mul_sum_min hy0.le N hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
    rcases le_total (p : ℝ) y with hpy | hpy
    · have h2 := dA_sum_min_pow y (by linarith) p hp.two_le N
      have h3 : Real.log p ≤ Real.log y := Real.log_le_log hp0 hpy
      linarith
    · have h2 := mul_le_mul_of_nonneg_left (sum_min_le_div hy0.le N hp) hlogp
      have he : Real.exp 1 ≤ y := by linarith [Real.exp_one_lt_d9]
      have h4 : Real.log p / p ≤ Real.log y / y :=
        Real.log_div_self_antitoneOn he (le_trans he hpy) hpy
      have h5 : Real.log p * (2 * (y / p)) ≤ 2 * Real.log y := by
        have e : Real.log p * (2 * (y / p)) = 2 * y * (Real.log p / p) := by ring
        rw [e]
        calc 2 * y * (Real.log p / p) ≤ 2 * y * (Real.log y / y) := by gcongr
          _ = 2 * Real.log y := by field_simp
      linarith
  · have h0 : sP (cN y) N p = 0 := by
      unfold sP
      refine Finset.sum_eq_zero fun n hn => ?_
      rw [Finset.mem_filter] at hn
      obtain ⟨_, hpp, hmin⟩ := hn
      exact absurd (hmin ▸ Nat.minFac_prime hpp.ne_one) hp
    rw [h0]
    positivity

end QH
