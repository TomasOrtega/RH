import Mathlib

namespace GlobalTheory.UU

/- English proof (translation)
Break down `Nat.eq_zero_or_pos B with hB | hB` into its components or cases. Use `H 1` as an intermediate fact. Simplify using `[hB] at this`. Use linear arithmetic over natural numbers and integers. Assume the negation of the conclusion as `hAB`.

Use `push Not at hAB`. Establish `hBr : (0 : ℝ) < B` using `by exact_mod_cast hB`. Establish `hr : (1 : ℝ) < (A : ℝ) / B`. Rewrite using `[one_lt_div hBr]`. Conclude with `hAB` after adjusting the coercions.

Establish `ht` using `(tendsto_pow_const_div_const_pow_of_one_lt g hr).const_mul ((K : ℝ) * (1 + a) ^ g)`. Rewrite `ht` using `[mul_zero]`. Establish `h1 : ∀ᶠ k : ℕ in Filter.atTop, (1 : ℝ) ≤ ((K : ℝ) * (1 + a) ^ g) * ((k : ℝ) ^ g / ((A : ℝ) / B) ^ k)` using `by filter_upwards [Filter.eventually_ge_atTop 1] with k hk`. Establish `hk' : A ^ k ≤ K * B ^ k * ((1 + a) * k) ^ g`. Use `(H k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))` and prove the remaining obligations.

Use the polynomial consequences of the given equalities and inequalities. Establish `hk2 : (A : ℝ) ^ k ≤ K * (B : ℝ) ^ k * ((1 + a) * k) ^ g` using `by exact_mod_cast hk'`. Establish `hA : (0 : ℝ) < A` using `by exact_mod_cast (hB.trans hAB)`. Rewrite using `[div_pow, ← mul_div_assoc, div_div_eq_mul_div, one_le_div (by positivity)]`. Use `hk2.trans (le_of_eq ?_)` and prove the remaining obligations.

Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Use `ge_of_tendsto ht h1` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_of_pow_le_poly_mul_pow (A B K a g : ℕ)
    (H : ∀ k, A ^ k ≤ K * B ^ k * (1 + k * a) ^ g) : A ≤ B := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · have := H 1
    simp [hB] at this
    omega
  by_contra hAB
  push Not at hAB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr : (1 : ℝ) < (A : ℝ) / B := by
    rw [one_lt_div hBr]; exact_mod_cast hAB
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt g hr).const_mul
    ((K : ℝ) * (1 + a) ^ g)
  rw [mul_zero] at ht
  have h1 : ∀ᶠ k : ℕ in Filter.atTop,
      (1 : ℝ) ≤ ((K : ℝ) * (1 + a) ^ g) * ((k : ℝ) ^ g / ((A : ℝ) / B) ^ k) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk' : A ^ k ≤ K * B ^ k * ((1 + a) * k) ^ g := by
      refine (H k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      nlinarith
    have hk2 : (A : ℝ) ^ k ≤ K * (B : ℝ) ^ k * ((1 + a) * k) ^ g := by exact_mod_cast hk'
    have hA : (0 : ℝ) < A := by exact_mod_cast (hB.trans hAB)
    rw [div_pow, ← mul_div_assoc, div_div_eq_mul_div, one_le_div (by positivity)]
    refine hk2.trans (le_of_eq ?_)
    rw [mul_pow]; ring
  have := ge_of_tendsto ht h1
  linarith

/- English proof (translation)
Introduce `h g c C a d q hc hq hm hg hd`. Establish `h1 : 1 ≤ h 1`. Use `(hg 1 le_rfl).1` as an intermediate fact. Break down `Nat.eq_zero_or_pos (h 1) with h0 | h0` into its components or cases. Simplify using `[h0] at this`.

Conclude with `h0`. Establish `up : ∀ k t, h (q ^ k * t) ≤ d ^ k * h (t + k * a)`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => intro t`.

Simplify using the standard rewrite rules. Consider the case `succ k ih`. Introduce `t`. Establish `e1 : q ^ (k + 1) * t = q ^ k * (q * t)` using `by ring`. Rewrite using `[e1]`.

Use `(ih _).trans ?_` and prove the remaining obligations. Rewrite using `[pow_succ, mul_assoc]`. Use `Nat.mul_le_mul_left _ ?_` and prove the remaining obligations. Establish `e2 : t + (k + 1) * a = t + k * a + a` using `by ring`. Rewrite using `[e2]`.

Use `le_trans (hm _ _ ?_) (hd (t + k * a)).2` and prove the remaining obligations. Rewrite using `[mul_add]`. Conclude with `Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hq) _`. Establish `lo : ∀ k, d ^ k ≤ h (q ^ k * (1 + k * a))`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero => simpa using h1`. Consider the case `succ k ih`. Rewrite using `[pow_succ, mul_comm]`. Use `(Nat.mul_le_mul_left d ih).trans ((hd _).1.trans (hm _ _ ?_))` and prove the remaining obligations.

Establish `hp : 1 ≤ q ^ k` using `Nat.one_le_pow _ _ hq`. Establish `e : q ^ (k + 1) * (1 + (k + 1) * a) = q * (q ^ k * (1 + k * a) + q ^ k * a)` using `by ring`. Rewrite using `[e]`. Conclude with `Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hp) _)`. Apply `le_antisymm` to reduce the goal to its premises.

Apply `le_of_pow_le_poly_mul_pow d (q ^ g) C a g` to reduce the goal to its premises. Introduce `k`. Establish `hp : 1 ≤ q ^ k * (1 + k * a)` using `Nat.mul_pos (Nat.pow_pos hq) (by omega)`. Use `(lo k).trans ((hg _ hp).2.trans (le_of_eq ?_))` and prove the remaining obligations. Rewrite using `[mul_pow, ← pow_mul, ← pow_mul, mul_comm k g]`.

Expand and normalize the polynomial expressions, which then agree. Apply `le_of_pow_le_poly_mul_pow (q ^ g) d (c * C) a g` to reduce the goal to its premises. Introduce `k`. Establish `hp : 1 ≤ q ^ k` using `Nat.one_le_pow _ _ hq`. Establish `a1` using `(hg _ hp).1`.

Establish `a2` using `up k 1`. Rewrite `a2` using `[mul_one]`. Establish `a3` using `(hg (1 + k * a) (by omega)).2`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem degree_eq_pow_of_growth :
    ∀ (h : ℕ → ℕ) (g c C a d q : ℕ), 1 ≤ c → 1 ≤ q → (∀ t t', t ≤ t' → h t ≤ h t') → (∀ t, 1 ≤ t → t ^ g ≤ c * h t ∧ h t ≤ C * t ^ g) → (∀ t, d * h t ≤ h (q * (t + a)) ∧ h (q * t) ≤ d * h (t + a)) → d = q ^ g := by
  intro h g c C a d q hc hq hm hg hd
  have h1 : 1 ≤ h 1 := by
    have := (hg 1 le_rfl).1
    rcases Nat.eq_zero_or_pos (h 1) with h0 | h0
    · simp [h0] at this
    · exact h0
  have up : ∀ k t, h (q ^ k * t) ≤ d ^ k * h (t + k * a) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have e1 : q ^ (k + 1) * t = q ^ k * (q * t) := by ring
      rw [e1]
      refine (ih _).trans ?_
      rw [pow_succ, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      have e2 : t + (k + 1) * a = t + k * a + a := by ring
      rw [e2]
      refine le_trans (hm _ _ ?_) (hd (t + k * a)).2
      rw [mul_add]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hq) _
  have lo : ∀ k, d ^ k ≤ h (q ^ k * (1 + k * a)) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [pow_succ, mul_comm]
      refine (Nat.mul_le_mul_left d ih).trans ((hd _).1.trans (hm _ _ ?_))
      have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
      have e : q ^ (k + 1) * (1 + (k + 1) * a) = q * (q ^ k * (1 + k * a) + q ^ k * a) := by ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hp) _)
  apply le_antisymm
  · apply le_of_pow_le_poly_mul_pow d (q ^ g) C a g
    intro k
    have hp : 1 ≤ q ^ k * (1 + k * a) := Nat.mul_pos (Nat.pow_pos hq) (by omega)
    refine (lo k).trans ((hg _ hp).2.trans (le_of_eq ?_))
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k g]; ring
  · apply le_of_pow_le_poly_mul_pow (q ^ g) d (c * C) a g
    intro k
    have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    have a1 := (hg _ hp).1
    have a2 := up k 1
    rw [mul_one] at a2
    have a3 := (hg (1 + k * a) (by omega)).2
    calc (q ^ g) ^ k = (q ^ k) ^ g := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ c * h (q ^ k) := a1
      _ ≤ c * (d ^ k * (C * (1 + k * a) ^ g)) :=
        Nat.mul_le_mul_left _ (a2.trans (Nat.mul_le_mul_left _ a3))
      _ = _ := by ring

end GlobalTheory.UU
