import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.RestNonneg

open Formalism.L2.FormalSeriesBounds

/- English proof (translation)
Establish `hk0 : (0:ℝ) < k` using `by exact_mod_cast hk`. Establish `hk1 : (1:ℝ) ≤ k` using `by exact_mod_cast hk`. Establish `hlog : 0 ≤ Real.log k` using `Real.log_nonneg hk1`. Establish `hj1 : Real.log k < (⌊Real.log k⌋₊ : ℝ) + 1` using `Nat.lt_floor_add_one _`. Establish `hj2 : (⌊Real.log k⌋₊ : ℝ) ≤ Real.log k` using `Nat.floor_le hlog`.

Establish `hmem : 2 * ⌊Real.log k⌋₊ + 3 ∈ {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k:ℝ) ^ ((3:ℝ) / 2) < (l:ℝ) ^ i}`. Use `⟨⟨⌊Real.log k⌋₊ + 1, by ring⟩, by omega, ?_⟩` and prove the remaining obligations. Establish `e1 : (k:ℝ) ^ ((3:ℝ) / 2) ≤ (k:ℝ) ^ (2:ℝ)` using `Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)`. Establish `e2 : (k:ℝ) ^ (2:ℝ) = Real.exp (2 * Real.log k)`. Rewrite using `[Real.rpow_def_of_pos hk0, mul_comm]`.

Establish `e3 : Real.exp (2 * Real.log k) < Real.exp ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ)`. Apply `Real.exp_lt_exp.2` to reduce the goal to its premises. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e4 : Real.exp ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) ≤ (5:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3)`.

Rewrite using `[show ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) = ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) * 1 by ring, Real.exp_nat_mul]`. Apply `pow_le_pow_left₀ (Real.exp_pos 1).le` to reduce the goal to its premises. Use `Real.exp_one_lt_d9` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e5 : (5:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3) ≤ (l:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3)`.

Apply `pow_le_pow_left₀ (by norm_num)` to reduce the goal to its premises. Conclude with `hl` after adjusting the coercions. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hle : RF.i0 k l ≤ 2 * ⌊Real.log k⌋₊ + 3` using `Nat.sInf_le hmem`. Establish `hc : ((RF.i0 k l : ℕ) : ℝ) ≤ ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ)` using `by exact_mod_cast hle`.

Move the coercions through the operations in `at hc`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private lemma UpperTheory.least_level_le_log_bound (k l : ℕ) (hk : 1 ≤ k) (hl : 5 ≤ l) :
    ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * Real.log k := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1
  have hj1 : Real.log k < (⌊Real.log k⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hj2 : (⌊Real.log k⌋₊ : ℝ) ≤ Real.log k := Nat.floor_le hlog
  have hmem : 2 * ⌊Real.log k⌋₊ + 3 ∈
      {i : ℕ | Odd i ∧ 3 ≤ i ∧ (k:ℝ) ^ ((3:ℝ) / 2) < (l:ℝ) ^ i} := by
    refine ⟨⟨⌊Real.log k⌋₊ + 1, by ring⟩, by omega, ?_⟩
    have e1 : (k:ℝ) ^ ((3:ℝ) / 2) ≤ (k:ℝ) ^ (2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num)
    have e2 : (k:ℝ) ^ (2:ℝ) = Real.exp (2 * Real.log k) := by
      rw [Real.rpow_def_of_pos hk0, mul_comm]
    have e3 : Real.exp (2 * Real.log k) < Real.exp ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) := by
      apply Real.exp_lt_exp.2
      push_cast
      linarith
    have e4 : Real.exp ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) ≤ (5:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3) := by
      rw [show ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) = ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) * 1 by ring,
        Real.exp_nat_mul]
      apply pow_le_pow_left₀ (Real.exp_pos 1).le
      have := Real.exp_one_lt_d9
      linarith
    have e5 : (5:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3) ≤ (l:ℝ) ^ (2 * ⌊Real.log k⌋₊ + 3) := by
      apply pow_le_pow_left₀ (by norm_num)
      exact_mod_cast hl
    linarith
  have hle : RF.i0 k l ≤ 2 * ⌊Real.log k⌋₊ + 3 := Nat.sInf_le hmem
  have hc : ((RF.i0 k l : ℕ) : ℝ) ≤ ((2 * ⌊Real.log k⌋₊ + 3 : ℕ) : ℝ) := by exact_mod_cast hle
  push_cast at hc
  linarith

/- English proof (translation)
Introduce `r f n m nW l k L hm hmn hnr hf hk hL hlogL hW hl`. Establish `hk1 : 1 ≤ k` using `by omega`. Establish `hi` using `UpperTheory.least_level_le_log_bound k l hk1 hl`. Establish `hmR : (1:ℝ) ≤ m` using `by exact_mod_cast hm`. Establish `hmnR : (m:ℝ) ≤ n` using `by exact_mod_cast hmn`.

Establish `hnrR : (n:ℝ) ≤ r` using `by exact_mod_cast hnr`. Establish `hfR : (2:ℝ) ≤ f` using `by exact_mod_cast hf`. Establish `hn1 : (1:ℝ) ≤ n` using `le_trans hmR hmnR`. Establish `hr1 : (1:ℝ) ≤ r` using `le_trans hn1 hnrR`. Establish `hiL : ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * L` using `by linarith`.

Establish `hX : (0:ℝ) ≤ (f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2` using `by positivity`. Establish `hdiv : (f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2 ≤ (f:ℝ) ^ 2 * (n:ℝ) ^ 3 * L ^ 2 / m`. Rewrite using `[le_div_iff₀ (by linarith)]`. Use `mul_le_mul_of_nonneg_left hmnR hX` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `h1 : (f:ℝ) * (((RF.i0 k l : ℕ) : ℝ) + 1) * n ≤ f * (4 + 2 * L) * n`. Apply `mul_le_mul_of_nonneg_right _ (by linarith)` to reduce the goal to its premises. Apply `mul_le_mul_of_nonneg_left _ (by linarith)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Establish `a1 : 4 + 2 * L ≤ 10 * (f:ℝ) * L ^ 2`.

Use polynomial arithmetic with `[mul_nonneg (sub_nonneg.2 hfR) (sq_nonneg L)]`. Establish `hrn : (1:ℝ) ≤ r * n` using `by nlinarith`. Establish `a2 : (n:ℝ) ≤ r * (n:ℝ) ^ 2`. Use polynomial arithmetic with `[mul_le_mul_of_nonneg_left hrn (by linarith : (0:ℝ) ≤ n)]`. Establish `h2 : (f:ℝ) * (4 + 2 * L) * n ≤ 10 * r * ((f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2)`.

Combine the equalities or inequalities in the displayed calculation. Establish `h3` using `mul_le_mul_of_nonneg_left hdiv (by linarith : (0:ℝ) ≤ 10 * r)`. Establish `h4 : 4 * (f:ℝ) * r ≤ 10 * r * f` using `by nlinarith`. Establish `key : (((f * ((RF.i0 k l + 1) * n + 4 * r)) : ℕ) : ℝ) ≤ nW`. Use `push_cast`.

Use the polynomial consequences of the given equalities and inequalities. Conclude with `key` after adjusting the coercions.
-/
theorem UpperTheory.f_mul_leastAdmissibleLevel_rows_le :
    ∀ (r f n m nW l k : ℕ) (L : ℝ), 1 ≤ m → m ≤ n → n ≤ r → 2 ≤ f → n + 1 = k → 3 ≤ L → Real.log k ≤ L →
    10 * (r : ℝ) * (f + (f : ℝ) ^ 2 * (n : ℝ) ^ 3 * L ^ 2 / m) ≤ nW → 5 ≤ l → f * ((RF.i0 k l + 1) * n + 4 * r) ≤ nW := by
  intro r f n m nW l k L hm hmn hnr hf hk hL hlogL hW hl
  have hk1 : 1 ≤ k := by omega
  have hi := UpperTheory.least_level_le_log_bound k l hk1 hl
  have hmR : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hmnR : (m:ℝ) ≤ n := by exact_mod_cast hmn
  have hnrR : (n:ℝ) ≤ r := by exact_mod_cast hnr
  have hfR : (2:ℝ) ≤ f := by exact_mod_cast hf
  have hn1 : (1:ℝ) ≤ n := le_trans hmR hmnR
  have hr1 : (1:ℝ) ≤ r := le_trans hn1 hnrR
  have hiL : ((RF.i0 k l : ℕ) : ℝ) ≤ 3 + 2 * L := by linarith
  have hX : (0:ℝ) ≤ (f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2 := by positivity
  have hdiv : (f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2 ≤ (f:ℝ) ^ 2 * (n:ℝ) ^ 3 * L ^ 2 / m := by
    rw [le_div_iff₀ (by linarith)]
    have := mul_le_mul_of_nonneg_left hmnR hX
    nlinarith
  have h1 : (f:ℝ) * (((RF.i0 k l : ℕ) : ℝ) + 1) * n ≤ f * (4 + 2 * L) * n := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    apply mul_le_mul_of_nonneg_left _ (by linarith)
    linarith
  have a1 : 4 + 2 * L ≤ 10 * (f:ℝ) * L ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.2 hfR) (sq_nonneg L)]
  have hrn : (1:ℝ) ≤ r * n := by nlinarith
  have a2 : (n:ℝ) ≤ r * (n:ℝ) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hrn (by linarith : (0:ℝ) ≤ n)]
  have h2 : (f:ℝ) * (4 + 2 * L) * n ≤ 10 * r * ((f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2) := by
    calc (f:ℝ) * (4 + 2 * L) * n ≤ f * (10 * f * L ^ 2) * n := by gcongr
      _ = 10 * (f:ℝ) ^ 2 * L ^ 2 * n := by ring
      _ ≤ 10 * (f:ℝ) ^ 2 * L ^ 2 * (r * (n:ℝ) ^ 2) := by gcongr
      _ = 10 * r * ((f:ℝ) ^ 2 * (n:ℝ) ^ 2 * L ^ 2) := by ring
  have h3 := mul_le_mul_of_nonneg_left hdiv (by linarith : (0:ℝ) ≤ 10 * r)
  have h4 : 4 * (f:ℝ) * r ≤ 10 * r * f := by nlinarith
  have key : (((f * ((RF.i0 k l + 1) * n + 4 * r)) : ℕ) : ℝ) ≤ nW := by
    push_cast
    nlinarith
  exact_mod_cast key
