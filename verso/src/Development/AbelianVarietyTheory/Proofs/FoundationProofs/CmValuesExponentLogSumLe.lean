import Mathlib
import Formalism.PairingDivisors.StatementN

open Finset

namespace GlobalTheory

/- English proof (translation)
Establish `h1 : ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l = ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[Nat.factorization_def X (hS l hl)]`. Rewrite using `[h1, Real.log_nat_eq_sum_factorization, Finsupp.sum]`. Establish `hsub : S ⊆ S ∪ X.factorization.support` using `Finset.subset_union_left`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum_of_subset_of_nonneg hsub fun l hl _ => ?_` and prove the remaining obligations. Break down `Finset.mem_union.1 hl with h | h` into its components or cases. Conclude with `mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast (hS l h).one_lt.le))`. Establish `hp : l.Prime` using `Nat.prime_of_mem_primeFactors (by simpa using h)`.

Conclude with `mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))`. Use `_ = ∑ l ∈ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by`. Use `(Finset.sum_subset Finset.subset_union_right fun l _ hl => ?_).symm` and prove the remaining obligations. Rewrite using `[Finsupp.notMem_support_iff.1 hl]`. Simplify using the standard rewrite rules.
-/
theorem ceSum_val_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (X : ℕ) :
    ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l ≤ Real.log X := by
  have h1 : ∑ l ∈ S, (padicValNat l X : ℝ) * Real.log l
      = ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l := by
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Nat.factorization_def X (hS l hl)]
  rw [h1, Real.log_nat_eq_sum_factorization, Finsupp.sum]
  have hsub : S ⊆ S ∪ X.factorization.support := Finset.subset_union_left
  calc ∑ l ∈ S, (X.factorization l : ℝ) * Real.log l
      ≤ ∑ l ∈ S ∪ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by
        refine Finset.sum_le_sum_of_subset_of_nonneg hsub fun l hl _ => ?_
        rcases Finset.mem_union.1 hl with h | h
        · exact mul_nonneg (Nat.cast_nonneg _)
            (Real.log_nonneg (by exact_mod_cast (hS l h).one_lt.le))
        · have hp : l.Prime := Nat.prime_of_mem_primeFactors (by simpa using h)
          exact mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    _ = ∑ l ∈ X.factorization.support, (X.factorization l : ℝ) * Real.log l := by
        refine (Finset.sum_subset Finset.subset_union_right fun l _ hl => ?_).symm
        rw [Finsupp.notMem_support_iff.1 hl]
        simp

/- English proof (translation)
Rewrite using `[← Finset.sum_filter]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum_of_subset_of_nonneg ?_ fun l hl _ => ?_` and prove the remaining obligations. Introduce `l hl`. Break down `Finset.mem_filter.1 hl with ⟨hlS, hln⟩` into its components or cases.

Conclude with `Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hS l hlS⟩`. Conclude with `Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hl).2.one_lt.le)`. Use `_ = Real.log (primorial n : ℝ) := by`. Rewrite using `[primorial, Nat.cast_prod, Real.log_prod]`. Introduce `l hl`.

Conclude with `(Finset.mem_filter.1 hl).2.ne_zero` after adjusting the coercions. Use `_ ≤ Real.log ((4 : ℝ) ^ n) := by`. Apply `Real.log_le_log (by exact_mod_cast primorial_pos n)` to reduce the goal to its premises. Conclude with `primorial_le_four_pow n` after adjusting the coercions. Use `_ = n * Real.log 4 := by rw [Real.log_pow]`.
-/
theorem ceSum_small_le (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) (n : ℕ) :
    ∑ l ∈ S, (if l ≤ n then Real.log l else 0) ≤ n * Real.log 4 := by
  rw [← Finset.sum_filter]
  calc ∑ l ∈ S.filter (· ≤ n), Real.log (l : ℝ)
      ≤ ∑ l ∈ (Finset.range (n + 1)).filter Nat.Prime, Real.log (l : ℝ) := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun l hl _ => ?_
        · intro l hl
          rcases Finset.mem_filter.1 hl with ⟨hlS, hln⟩
          exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hS l hlS⟩
        · exact Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.1 hl).2.one_lt.le)
    _ = Real.log (primorial n : ℝ) := by
        rw [primorial, Nat.cast_prod, Real.log_prod]
        intro l hl
        exact_mod_cast (Finset.mem_filter.1 hl).2.ne_zero
    _ ≤ Real.log ((4 : ℝ) ^ n) := by
        apply Real.log_le_log (by exact_mod_cast primorial_pos n)
        exact_mod_cast primorial_le_four_pow n
    _ = n * Real.log 4 := by rw [Real.log_pow]

end GlobalTheory

namespace GlobalTheory

open Formalism.PairingDivisionLocalBalance in

/- English proof (translation)
Establish `hlog : 0 ≤ Real.log (l : ℝ)` using `Real.log_nonneg (by exact_mod_cast hp.one_lt.le)`. Establish `hv : (0 : ℝ) ≤ padicValNat l X` using `Nat.cast_nonneg _`. Establish `hvl : 0 ≤ (padicValNat l X : ℝ) * Real.log l` using `mul_nonneg hv hlog`. Establish `hB : 0 ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)` using `by split_ifs`. Conclude with `Real.log_nonneg (by have : (0 : ℝ) ≤ X := Nat.cast_nonneg _; linarith)`.

Conclude with `le_rfl`. Establish `hC : 0 ≤ (if l ≤ X / 2 + 1 then Real.log l else 0)` using `by split_ifs`. Conclude with `hlog`. Conclude with `le_rfl`. Distinguish the cases in `h2 : l = 2`.

Substitute `h2` using the available equality. Establish `hlog2 : 0 ≤ Real.log (2 : ℝ)` using `Real.log_nonneg (by norm_num)`. Establish `hm : mE 2 X = 2 + padicValNat 2 X` using `by simp [mE]`. Establish `h22 : padicValNat 2 2 = 1` using `by simp`. Establish `e : ((f * padicValNat 2 2 + mE 2 X : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ) = (padicValNat 2 X : ℝ) * Real.log ((2 : ℕ) : ℝ) + ((f : ℝ) + 2) * Real.log 2`.

Rewrite using `[hm, h22]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[if_pos rfl, e]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hA : (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0) = 0` using `if_neg h2`. Establish `hv2 : padicValNat l 2 = 0`. Apply `padicValNat.eq_zero_of_not_dvd` to reduce the goal to its premises. Introduce `h`. Conclude with `h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)`.

Rewrite using `[hA, hv2]`. Distinguish the cases in `hd : (l - 1) ∣ X`. Establish `hm : mE l X = 1 + padicValNat l X` using `by simp [mE, h2, hd]`. Rewrite using `[hm]`. Use `push_cast`.

Establish `key : Real.log (l : ℝ) ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0) + (if l ≤ X / 2 + 1 then Real.log l else 0)`. Distinguish the cases in `hXl : l = X + 1`. Rewrite using `[if_pos hXl]`. Establish `: (l : ℝ) = (X : ℝ) + 1` using `by exact_mod_cast hXl`. Establish `e : Real.log (l : ℝ) = Real.log ((X : ℝ) + 1)` using `by rw [this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[if_neg hXl]`. Establish `hl3 : 3 ≤ l` using `by have := hp.two_le; omega`. Take `⟨k, hk⟩` from `hd`. Establish `hk0 : k ≠ 0` using `by rintro rfl; simp at hk; exact hX hk`.

Establish `hk1 : k ≠ 1` using `by rintro rfl; apply hXl; omega`. Establish `hk2 : (l - 1) * 2 ≤ (l - 1) * k` using `Nat.mul_le_mul_left _ (by omega)`. Establish `hle : l - 1 ≤ X / 2`. Rewrite using `[Nat.le_div_iff_mul_le (by norm_num)]`. Rewrite using `[hk]`.

Conclude with `hk2`. Rewrite using `[if_pos (by omega)]`. Combine the linear equalities and inequalities to obtain the conclusion. Use the polynomial consequences of the given equalities and inequalities. Establish `hm : mE l X = 0` using `by simp [mE, h2, hd]`.

Rewrite using `[hm]`. Simplify using `only [mul_zero, add_zero, Nat.cast_zero, zero_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ceSum_term_le (f X l : ℕ) (hX : X ≠ 0) (hp : l.Prime) :
    ((f * padicValNat l 2 + mE l X : ℕ) : ℝ) * Real.log l ≤
      (padicValNat l X : ℝ) * Real.log l + (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0)
        + (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
        + (if l ≤ X / 2 + 1 then Real.log l else 0) := by
  have hlog : 0 ≤ Real.log (l : ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hv : (0 : ℝ) ≤ padicValNat l X := Nat.cast_nonneg _
  have hvl : 0 ≤ (padicValNat l X : ℝ) * Real.log l := mul_nonneg hv hlog
  have hB : 0 ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0) := by
    split_ifs
    · exact Real.log_nonneg (by have : (0 : ℝ) ≤ X := Nat.cast_nonneg _; linarith)
    · exact le_rfl
  have hC : 0 ≤ (if l ≤ X / 2 + 1 then Real.log l else 0) := by
    split_ifs
    · exact hlog
    · exact le_rfl
  by_cases h2 : l = 2
  · subst h2
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hm : mE 2 X = 2 + padicValNat 2 X := by simp [mE]
    have h22 : padicValNat 2 2 = 1 := by simp
    have e : ((f * padicValNat 2 2 + mE 2 X : ℕ) : ℝ) * Real.log ((2 : ℕ) : ℝ)
        = (padicValNat 2 X : ℝ) * Real.log ((2 : ℕ) : ℝ) + ((f : ℝ) + 2) * Real.log 2 := by
      rw [hm, h22]; push_cast; ring
    rw [if_pos rfl, e]
    linarith
  · have hA : (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0) = 0 := if_neg h2
    have hv2 : padicValNat l 2 = 0 := by
      apply padicValNat.eq_zero_of_not_dvd
      intro h
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
    rw [hA, hv2]
    by_cases hd : (l - 1) ∣ X
    · have hm : mE l X = 1 + padicValNat l X := by simp [mE, h2, hd]
      rw [hm]
      push_cast
      have key : Real.log (l : ℝ) ≤ (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
          + (if l ≤ X / 2 + 1 then Real.log l else 0) := by
        by_cases hXl : l = X + 1
        · rw [if_pos hXl]
          have : (l : ℝ) = (X : ℝ) + 1 := by exact_mod_cast hXl
          have e : Real.log (l : ℝ) = Real.log ((X : ℝ) + 1) := by rw [this]
          linarith
        · rw [if_neg hXl]
          have hl3 : 3 ≤ l := by have := hp.two_le; omega
          obtain ⟨k, hk⟩ := hd
          have hk0 : k ≠ 0 := by rintro rfl; simp at hk; exact hX hk
          have hk1 : k ≠ 1 := by rintro rfl; apply hXl; omega
          have hk2 : (l - 1) * 2 ≤ (l - 1) * k := Nat.mul_le_mul_left _ (by omega)
          have hle : l - 1 ≤ X / 2 := by
            rw [Nat.le_div_iff_mul_le (by norm_num)]
            rw [hk]; exact hk2
          rw [if_pos (by omega)]
          linarith
      nlinarith
    · have hm : mE l X = 0 := by simp [mE, h2, hd]
      rw [hm]
      simp only [mul_zero, add_zero, Nat.cast_zero, zero_mul]
      linarith

end GlobalTheory

namespace GlobalTheory

/- English proof (translation)
Introduce `f X S hX hfX hS`. Establish `hX0 : X ≠ 0` using `by omega`. Establish `hsum` using `Finset.sum_le_sum fun l hl => ceSum_term_le f X l hX0 (hS l hl)`. Rewrite `hsum` using `[Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]`. Establish `hv` using `ceSum_val_le S hS X`.

Establish `hs` using `ceSum_small_le S hS (X / 2 + 1)`. Establish `hlog2 : 0 ≤ Real.log (2 : ℝ)` using `Real.log_nonneg (by norm_num)`. Establish `hXr : (16 : ℝ) ≤ X` using `by exact_mod_cast hX`. Establish `hL0 : 0 ≤ Real.log ((X : ℝ) + 1)` using `Real.log_nonneg (by linarith)`. Establish `hA : ∑ l ∈ S, (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0) ≤ ((f : ℝ) + 2) * Real.log 2`.

Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs`. Conclude with `le_rfl`. Check the signs of the components of the expression. Establish `hB : ∑ l ∈ S, (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0) ≤ Real.log ((X : ℝ) + 1)`.

Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs`. Conclude with `le_rfl`. Conclude with `hL0`. Establish `hlogX : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 1)` using `Real.log_le_log (by linarith) (by linarith)`.

Establish `hL4 : 4 * Real.log 2 ≤ Real.log ((X : ℝ) + 1)`. Establish `: Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2` using `by rw [Real.log_pow]; norm_num`. Rewrite using `[← this]`. Conclude with `Real.log_le_log (by norm_num) (by norm_num; linarith)`. Establish `h4 : Real.log (4 : ℝ) = 2 * Real.log 2`.

Establish `: (4 : ℝ) = 2 ^ 2` using `by norm_num`. Rewrite using `[this, Real.log_pow]`. Evaluate the numerical expressions. Establish `hn : (((X / 2 + 1 : ℕ)) : ℝ) * 2 ≤ X + 2`. Establish `: (X / 2 + 1) * 2 ≤ X + 2` using `by omega`.

Conclude with `this` after adjusting the coercions. Establish `hf : (f : ℝ) * 2 ≤ X` using `by exact_mod_cast (by omega : f * 2 ≤ X)`. Rewrite `hs` using `[h4]`. Establish `p1 : 0 ≤ ((X : ℝ) - 2 * f) * Real.log 2` using `mul_nonneg (by linarith) hlog2`. Establish `p2 : 0 ≤ ((X : ℝ) + 2 - ((X / 2 + 1 : ℕ) : ℝ) * 2) * Real.log 2` using `mul_nonneg (by linarith) hlog2`.

Establish `p3 : 0 ≤ ((X : ℝ) - 2) * (Real.log ((X : ℝ) + 1) - 4 * Real.log 2)` using `mul_nonneg (by linarith) (by linarith)`. Establish `p4 : 0 ≤ ((X : ℝ) - 16) * Real.log 2` using `mul_nonneg (by linarith) hlog2`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem dividedPowerValuations_cESum : Formalism.PairingDivisionLocalBalance.CESum := by
  intro f X S hX hfX hS
  have hX0 : X ≠ 0 := by omega
  have hsum := Finset.sum_le_sum fun l hl => ceSum_term_le f X l hX0 (hS l hl)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hv := ceSum_val_le S hS X
  have hs := ceSum_small_le S hS (X / 2 + 1)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hXr : (16 : ℝ) ≤ X := by exact_mod_cast hX
  have hL0 : 0 ≤ Real.log ((X : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hA : ∑ l ∈ S, (if l = 2 then ((f : ℝ) + 2) * Real.log 2 else 0)
      ≤ ((f : ℝ) + 2) * Real.log 2 := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · positivity
  have hB : ∑ l ∈ S, (if l = X + 1 then Real.log ((X : ℝ) + 1) else 0)
      ≤ Real.log ((X : ℝ) + 1) := by
    rw [Finset.sum_ite_eq']
    split_ifs
    · exact le_rfl
    · exact hL0
  have hlogX : Real.log (X : ℝ) ≤ Real.log ((X : ℝ) + 1) :=
    Real.log_le_log (by linarith) (by linarith)
  have hL4 : 4 * Real.log 2 ≤ Real.log ((X : ℝ) + 1) := by
    have : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [← this]
    exact Real.log_le_log (by norm_num) (by norm_num; linarith)
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]; norm_num
  have hn : (((X / 2 + 1 : ℕ)) : ℝ) * 2 ≤ X + 2 := by
    have : (X / 2 + 1) * 2 ≤ X + 2 := by omega
    exact_mod_cast this
  have hf : (f : ℝ) * 2 ≤ X := by exact_mod_cast (by omega : f * 2 ≤ X)
  rw [h4] at hs
  have p1 : 0 ≤ ((X : ℝ) - 2 * f) * Real.log 2 := mul_nonneg (by linarith) hlog2
  have p2 : 0 ≤ ((X : ℝ) + 2 - ((X / 2 + 1 : ℕ) : ℝ) * 2) * Real.log 2 :=
    mul_nonneg (by linarith) hlog2
  have p3 : 0 ≤ ((X : ℝ) - 2) * (Real.log ((X : ℝ) + 1) - 4 * Real.log 2) :=
    mul_nonneg (by linarith) (by linarith)
  have p4 : 0 ≤ ((X : ℝ) - 16) * Real.log 2 := mul_nonneg (by linarith) hlog2
  nlinarith

end GlobalTheory
