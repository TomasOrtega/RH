import Mathlib

open scoped BigOperators Matrix
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `h` using `Nat.add_one_mul_choose_eq (c + n) n`. Establish `h' : (c + (n + 1)).choose (n + 1) * (n + 1) = (c + n + 1) * (c + n).choose n`. Rewrite using `[show c + (n + 1) = c + n + 1 by ring]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `h'` after adjusting the coercions.
-/
private theorem choose_succ_mul_succ_eq_mul_choose (c n : ℕ) :
    (((c + (n + 1)).choose (n + 1) : ℕ) : ℝ) * ((n : ℝ) + 1)
      = ((c : ℝ) + n + 1) * (((c + n).choose n : ℕ) : ℝ) := by
  have h := Nat.add_one_mul_choose_eq (c + n) n
  have h' : (c + (n + 1)).choose (n + 1) * (n + 1) = (c + n + 1) * (c + n).choose n := by
    rw [show c + (n + 1) = c + n + 1 by ring]
    linarith
  exact_mod_cast h'

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Establish `hpos : (0 : ℝ) < (n : ℝ) + 1` using `by positivity`. Establish `hA` using `choose_succ_mul_succ_eq_mul_choose a n`.

Establish `hB` using `choose_succ_mul_succ_eq_mul_choose b n`. Establish `hCa : (0 : ℝ) ≤ (((a + n).choose n : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hCb : (0 : ℝ) ≤ (((b + n).choose n : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hn : (0 : ℝ) ≤ n` using `Nat.cast_nonneg _`. Establish `hlin : (a : ℝ) + n + 1 ≤ (1 + y) * ((b : ℝ) + n + 1)`.

Use polynomial arithmetic with `[mul_nonneg hy hn]`. Establish `hfac : (0 : ℝ) ≤ (1 + y) * ((b : ℝ) + n + 1)` using `mul_nonneg (by linarith) (by positivity)`. Establish `hpow : (0 : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ)` using `mul_nonneg (pow_nonneg (by linarith) n) hCb`. Rewrite using `[← mul_le_mul_iff_of_pos_right hpos]`. Rewrite using `[hA, mul_assoc, hB]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem choose_add_le_pow_mul_choose_add (a b : ℕ) (y : ℝ) (hy : 0 ≤ y)
    (h : (a : ℝ) ≤ b + y * (b + 1)) (n : ℕ) :
    (((a + n).choose n : ℕ) : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hA := choose_succ_mul_succ_eq_mul_choose a n
    have hB := choose_succ_mul_succ_eq_mul_choose b n
    have hCa : (0 : ℝ) ≤ (((a + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hCb : (0 : ℝ) ≤ (((b + n).choose n : ℕ) : ℝ) := Nat.cast_nonneg _
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hlin : (a : ℝ) + n + 1 ≤ (1 + y) * ((b : ℝ) + n + 1) := by
      nlinarith [mul_nonneg hy hn]
    have hfac : (0 : ℝ) ≤ (1 + y) * ((b : ℝ) + n + 1) :=
      mul_nonneg (by linarith) (by positivity)
    have hpow : (0 : ℝ) ≤ (1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ) :=
      mul_nonneg (pow_nonneg (by linarith) n) hCb
    rw [← mul_le_mul_iff_of_pos_right hpos]
    rw [hA, mul_assoc, hB]
    calc ((a : ℝ) + n + 1) * (((a + n).choose n : ℕ) : ℝ)
        ≤ ((1 + y) * ((b : ℝ) + n + 1)) * ((1 + y) ^ n * (((b + n).choose n : ℕ) : ℝ)) :=
          mul_le_mul hlin ih hCa hfac
      _ = (1 + y) ^ (n + 1) * (((b : ℝ) + n + 1) * (((b + n).choose n : ℕ) : ℝ)) := by ring

/- English proof (translation)
Establish `hx : |x| ≤ 1` using `by rw [abs_of_nonneg h0]; linarith`. Establish `hb` using `Real.exp_bound hx (n := 3) (by norm_num)`. Establish `h2` using `(abs_le.mp hb).2`. Rewrite `h2` using `[abs_of_nonneg h0]`. Simplify using `only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2`.

Evaluate the numerical expressions using `at h2`. Establish `hx2 : x ^ 2 ≤ x / 10` using `by nlinarith`. Establish `hx3 : x ^ 3 ≤ x / 100` using `by nlinarith`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem exp_le_one_add_of_le_tenth (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1 / 10) :
    Real.exp x ≤ 1 + 53 / 50 * x := by
  have hx : |x| ≤ 1 := by rw [abs_of_nonneg h0]; linarith
  have hb := Real.exp_bound hx (n := 3) (by norm_num)
  have h2 := (abs_le.mp hb).2
  rw [abs_of_nonneg h0] at h2
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have hx2 : x ^ 2 ≤ x / 10 := by nlinarith
  have hx3 : x ^ 3 ≤ x / 100 := by nlinarith
  nlinarith

/- English proof (translation)
Introduce `D T a ρ hD hT hρ0 hρ1 ha hε`. Establish `hD' : (2 : ℝ) ≤ D` using `by exact_mod_cast hD`. Establish `hT' : (20 : ℝ) * D ≤ T` using `by exact_mod_cast hT`. Establish `hTpos : (0 : ℝ) < T` using `by linarith`. Establish `hbD : (T - 1 - D) + D = T - 1` using `by omega`.

Establish `hbR : ((T - 1 - D : ℕ) : ℝ) = T - 1 - D`. Establish `h3 : (T - 1 - D) + D + 1 = T` using `by omega`. Establish `h` using `congrArg (fun k : ℕ => (k : ℝ)) h3`. Move the coercions through the operations in `at h`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hρ' : 0 < 1 - ρ` using `by linarith`. Establish `hTD : 0 < (T : ℝ) - D` using `by linarith`. Establish `hden : 0 < (1 - ρ) * ((T : ℝ) - D)` using `mul_pos hρ' hTD`. Establish `hnum0 : (0 : ℝ) ≤ 2 * D + 5 + ρ * T` using `by nlinarith [mul_nonneg hρ0 hTpos.le]`. Establish `hy0 : (0 : ℝ) ≤ (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))` using `div_nonneg hnum0 hden.le`.

Establish `hyb : (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1) = (2 * D + 5 + ρ * T) / (1 - ρ)`. Rewrite using `[hbR]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hab : (a : ℝ) ≤ ((T - 1 - D : ℕ) : ℝ) + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1)`.

Rewrite using `[hyb, hbR]`. Establish `key : ((T : ℝ) + D + 4) / (1 - ρ) ≤ (T - 1 - D) + (2 * D + 5 + ρ * T) / (1 - ρ)`. Rewrite using `[div_le_iff₀ hρ', add_mul, div_mul_cancel₀ _ hρ'.ne']`. Use polynomial arithmetic with `[mul_nonneg hρ0 (by linarith : (0 : ℝ) ≤ D + 1)]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1` using `choose_add_le_pow_mul_choose_add a (T - 1 - D) _ hy0 hab D`. Rewrite `h1` using `[hbD]`. Establish `hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hDy : (D : ℝ) * ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) = (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))` using `by ring`. Establish `hε0 : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))`.

Rewrite using `[← hDy]`. Conclude with `mul_nonneg (Nat.cast_nonneg _) hy0`. Establish `hpow : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D ≤ Real.exp ((D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))`. Rewrite using `[← hDy, Real.exp_nat_mul]`. Conclude with `pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))]) D`.

Establish `hexp` using `exp_le_one_add_of_le_tenth _ hε0 hε`. Establish `hu : (57 / 80 : ℝ) * T ≤ (1 - ρ) * (T - D)`. Use polynomial arithmetic with `[mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - ρ) hTD.le]`. Establish `hnum : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T)` using `mul_nonneg (Nat.cast_nonneg _) hnum0`. Establish `h2 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T)` using `div_le_div_of_nonneg_left hnum (by positivity) hu`.

Establish `e1 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T) = (80 / 57) * ((D : ℝ) * (2 * D + 5) / T) + (80 / 57) * ((D : ℝ) * ρ)`. Clear the denominators using the available nonvanishing facts. Establish `e2 : (D : ℝ) * (2 * D + 5) / T ≤ (9 / 2) * ((D : ℝ) ^ 2 / T)`. Rewrite using `[mul_div_assoc']`. Conclude with `div_le_div_of_nonneg_right (by nlinarith) hTpos.le`.

Establish `e3 : 7 * (D : ℝ) ^ 2 / T = 7 * ((D : ℝ) ^ 2 / T)` using `by ring`. Establish `hq : (0 : ℝ) ≤ (D : ℝ) ^ 2 / T` using `by positivity`. Establish `hdr : (0 : ℝ) ≤ (D : ℝ) * ρ` using `mul_nonneg (Nat.cast_nonneg _) hρ0`. Establish `hfin : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D ≤ 1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)`. Rewrite using `[e3]`.

Use the polynomial consequences of the given equalities and inequalities. Combine the equalities or inequalities in the displayed calculation.
-/
theorem choose_rank_ratio_le :
    ∀ (D T a : ℕ) (ρ : ℝ), 2 ≤ D → 20 * D ≤ T → 0 ≤ ρ → ρ ≤ 1 / 4 → (a : ℝ) ≤ ((T : ℝ) + D + 4) / (1 - ρ) → (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) ≤ 1 / 10 → (((a + D).choose D : ℕ) : ℝ) ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) := by
  intro D T a ρ hD hT hρ0 hρ1 ha hε
  have hD' : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hT' : (20 : ℝ) * D ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by linarith
  have hbD : (T - 1 - D) + D = T - 1 := by omega
  have hbR : ((T - 1 - D : ℕ) : ℝ) = T - 1 - D := by
    have h3 : (T - 1 - D) + D + 1 = T := by omega
    have h := congrArg (fun k : ℕ => (k : ℝ)) h3
    push_cast at h
    linarith
  have hρ' : 0 < 1 - ρ := by linarith
  have hTD : 0 < (T : ℝ) - D := by linarith
  have hden : 0 < (1 - ρ) * ((T : ℝ) - D) := mul_pos hρ' hTD
  have hnum0 : (0 : ℝ) ≤ 2 * D + 5 + ρ * T := by nlinarith [mul_nonneg hρ0 hTpos.le]
  have hy0 : (0 : ℝ) ≤ (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := div_nonneg hnum0 hden.le
  have hyb : (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1)
      = (2 * D + 5 + ρ * T) / (1 - ρ) := by
    rw [hbR]
    field_simp
    ring
  have hab : (a : ℝ) ≤ ((T - 1 - D : ℕ) : ℝ)
      + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) * (((T - 1 - D : ℕ) : ℝ) + 1) := by
    rw [hyb, hbR]
    have key : ((T : ℝ) + D + 4) / (1 - ρ) ≤ (T - 1 - D) + (2 * D + 5 + ρ * T) / (1 - ρ) := by
      rw [div_le_iff₀ hρ', add_mul, div_mul_cancel₀ _ hρ'.ne']
      nlinarith [mul_nonneg hρ0 (by linarith : (0 : ℝ) ≤ D + 1)]
    linarith
  have h1 := choose_add_le_pow_mul_choose_add a (T - 1 - D) _ hy0 hab D
  rw [hbD] at h1
  have hC : (0 : ℝ) ≤ (((T - 1).choose D : ℕ) : ℝ) := Nat.cast_nonneg _
  have hDy : (D : ℝ) * ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))
      = (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by ring
  have hε0 : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)) := by
    rw [← hDy]; exact mul_nonneg (Nat.cast_nonneg _) hy0
  have hpow : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ Real.exp ((D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) := by
    rw [← hDy, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith)
      (by linarith [Real.add_one_le_exp ((2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D)))]) D
  have hexp := exp_le_one_add_of_le_tenth _ hε0 hε
  have hu : (57 / 80 : ℝ) * T ≤ (1 - ρ) * (T - D) := by
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 1 / 4 - ρ) hTD.le]
  have hnum : (0 : ℝ) ≤ (D : ℝ) * (2 * D + 5 + ρ * T) := mul_nonneg (Nat.cast_nonneg _) hnum0
  have h2 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))
      ≤ (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T) :=
    div_le_div_of_nonneg_left hnum (by positivity) hu
  have e1 : (D : ℝ) * (2 * D + 5 + ρ * T) / ((57 / 80) * T)
      = (80 / 57) * ((D : ℝ) * (2 * D + 5) / T) + (80 / 57) * ((D : ℝ) * ρ) := by
    field_simp
  have e2 : (D : ℝ) * (2 * D + 5) / T ≤ (9 / 2) * ((D : ℝ) ^ 2 / T) := by
    rw [mul_div_assoc']
    exact div_le_div_of_nonneg_right (by nlinarith) hTpos.le
  have e3 : 7 * (D : ℝ) ^ 2 / T = 7 * ((D : ℝ) ^ 2 / T) := by ring
  have hq : (0 : ℝ) ≤ (D : ℝ) ^ 2 / T := by positivity
  have hdr : (0 : ℝ) ≤ (D : ℝ) * ρ := mul_nonneg (Nat.cast_nonneg _) hρ0
  have hfin : (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D
      ≤ 1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ) := by
    rw [e3]
    nlinarith
  calc (((a + D).choose D : ℕ) : ℝ)
      ≤ (1 + (2 * D + 5 + ρ * T) / ((1 - ρ) * (T - D))) ^ D * (((T - 1).choose D : ℕ) : ℝ) := h1
    _ ≤ (1 + (7 * (D : ℝ) ^ 2 / T + 3 / 2 * D * ρ)) * (((T - 1).choose D : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hfin hC

end GlobalTheory
