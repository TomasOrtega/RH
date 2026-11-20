import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.T0

/- English proof (translation)
Establish `h1` using `Nat.choose_succ_right_eq n k`. Establish `h2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k` using `Nat.cast_sub h`. Rewrite using `[← h2]`. Conclude with `h1` after adjusting the coercions.
-/
private theorem choose_succ_mul_succ_eq_choose_mul_sub (n k : ℕ) (h : k ≤ n) :
    ((n.choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((n.choose k : ℕ) : ℝ) * ((n : ℝ) - k) := by
  have h1 := Nat.choose_succ_right_eq n k
  have h2 : ((n - k : ℕ) : ℝ) = (n : ℝ) - k := Nat.cast_sub h
  rw [← h2]
  exact_mod_cast h1

/- English proof (translation)
Introduce `k hk`. Proceed by induction on `k with`. Consider the case `zero => simp`. Consider the case `succ k ih`. Establish `ih` using `ih (by omega)`.

Establish `h7 : 7 * D ≤ T` using `by nlinarith [Nat.zero_le (D * D)]`. Establish `hA` using `choose_succ_mul_succ_eq_choose_mul_sub (T + 2 * D + 6) k (by omega)`. Establish `hB` using `choose_succ_mul_succ_eq_choose_mul_sub (T - 1) k (by omega)`. Establish `ha : ((T + 2 * D + 6 : ℕ) : ℝ) = (T : ℝ) + 2 * D + 6` using `by push_cast; ring`. Establish `hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1`.

Rewrite using `[Nat.cast_sub (by omega)]; simp`. Rewrite `hA` using `[ha]`. Rewrite `hB` using `[hT1]`. Establish `hkT : ((k : ℝ) + 2) ≤ T` using `by exact_mod_cast (show k + 2 ≤ T by omega)`. Establish `hb : (0 : ℝ) ≤ (T : ℝ) - 1 - k` using `by linarith`.

Establish `hCA : (0 : ℝ) ≤ (((T + 2 * D + 6).choose k : ℕ) : ℝ)` using `Nat.cast_nonneg _`. Establish `hk1 : (0 : ℝ) < (k : ℝ) + 1` using `by positivity`. Establish `hdiff : (0 : ℝ) ≤ ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) - ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k)`. Establish `e : ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) - ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) = (2 * (D : ℝ) + 7) * ((k : ℝ) + 1) * (2 * (D : ℝ) + 6)` using `by ring`. Rewrite using `[e]`.

Check the signs of the components of the expression. Establish `P` using `mul_le_mul_of_nonneg_right ih hb`. Establish `Q` using `mul_nonneg hCA hdiff`. Establish `key : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ≤ (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1)`. Establish `e1 : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((((T + 2 * D + 6).choose k : ℕ) : ℝ) * ((T : ℝ) + 2 * D + 6 - k))`.

Take the linear combination `((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * hA`. Establish `e2 : (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) = (T : ℝ) * ((((T - 1).choose k : ℕ) : ℝ) * ((T : ℝ) - 1 - k))`. Take the linear combination `(T : ℝ) * hB`. Rewrite using `[e1, e2]`. Use polynomial arithmetic with `[P, Q]`.

Use `push_cast`. Conclude with `le_of_mul_le_mul_right key hk1`.
-/
theorem sub_mul_choose_le_mul_choose (T D : ℕ) (hT : D * (2 * D + 7) ≤ T) :
    ∀ k ≤ D, ((T : ℝ) - k * (2 * D + 7)) * (((T + 2 * D + 6).choose k : ℕ) : ℝ) ≤
      (T : ℝ) * (((T - 1).choose k : ℕ) : ℝ) := by
  intro k hk
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    have h7 : 7 * D ≤ T := by nlinarith [Nat.zero_le (D * D)]
    have hA := choose_succ_mul_succ_eq_choose_mul_sub (T + 2 * D + 6) k (by omega)
    have hB := choose_succ_mul_succ_eq_choose_mul_sub (T - 1) k (by omega)
    have ha : ((T + 2 * D + 6 : ℕ) : ℝ) = (T : ℝ) + 2 * D + 6 := by push_cast; ring
    have hT1 : ((T - 1 : ℕ) : ℝ) = (T : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; simp
    rw [ha] at hA
    rw [hT1] at hB
    have hkT : ((k : ℝ) + 2) ≤ T := by exact_mod_cast (show k + 2 ≤ T by omega)
    have hb : (0 : ℝ) ≤ (T : ℝ) - 1 - k := by linarith
    have hCA : (0 : ℝ) ≤ (((T + 2 * D + 6).choose k : ℕ) : ℝ) := Nat.cast_nonneg _
    have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hdiff : (0 : ℝ) ≤ ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
        ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) := by
      have e : ((T : ℝ) - k * (2 * D + 7)) * ((T : ℝ) - 1 - k) -
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * ((T : ℝ) + 2 * D + 6 - k) =
          (2 * (D : ℝ) + 7) * ((k : ℝ) + 1) * (2 * (D : ℝ) + 6) := by ring
      rw [e]; positivity
    have P := mul_le_mul_of_nonneg_right ih hb
    have Q := mul_nonneg hCA hdiff
    have key : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
        (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) ≤
        (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) := by
      have e1 : ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          (((T + 2 * D + 6).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) *
          ((((T + 2 * D + 6).choose k : ℕ) : ℝ) * ((T : ℝ) + 2 * D + 6 - k)) := by
        linear_combination ((T : ℝ) - ((k : ℝ) + 1) * (2 * D + 7)) * hA
      have e2 : (T : ℝ) * (((T - 1).choose (k + 1) : ℕ) : ℝ) * ((k : ℝ) + 1) =
          (T : ℝ) * ((((T - 1).choose k : ℕ) : ℝ) * ((T : ℝ) - 1 - k)) := by
        linear_combination (T : ℝ) * hB
      rw [e1, e2]
      nlinarith [P, Q]
    push_cast
    exact le_of_mul_le_mul_right key hk1

end ReciprocityTheory.ChartRestriction.G.T0
