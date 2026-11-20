import Mathlib
import Formalism.FrobeniusOrbits.HostThickExists

open Finset

noncomputable section

namespace Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits

variable {α : Type*} [Fintype α]

/- English proof (translation)
Establish `h` using `Finset.sum_powerset_apply_card (fun k => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * f k) (x := (univ : Finset α))`. Rewrite `h` using `[powerset_univ, card_univ]`. Simplify using `only [bern]`. Rewrite using `[h]`. Use `sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Simplify using `[bernsteinPolynomial, nsmul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_card (δ : ℝ) (f : ℕ → ℝ) :
    ∑ T : Finset α, bern δ T * f T.card =
      ∑ k ∈ range (Fintype.card α + 1),
        (bernsteinPolynomial ℝ (Fintype.card α) k).eval δ * f k := by
  have h := Finset.sum_powerset_apply_card
    (fun k => δ ^ k * (1 - δ) ^ (Fintype.card α - k) * f k) (x := (univ : Finset α))
  rw [powerset_univ, card_univ] at h
  simp only [bern]
  rw [h]
  refine sum_congr rfl fun k _ => ?_
  simp [bernsteinPolynomial, nsmul_eq_mul]
  ring

/- English proof (translation)
Unfold `bern`. Establish `: 0 ≤ 1 - δ` using `by linarith`. Check the signs of the components of the expression.
-/
lemma bern_nonneg {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) (T : Finset α) : 0 ≤ bern δ T := by
  unfold bern
  have : 0 ≤ 1 - δ := by linarith
  positivity

/- English proof (translation)
Establish `h` using `sum_card (α := α) δ (fun _ => 1)`. Simplify using `only [mul_one] at h`. Rewrite using `[h, ← Polynomial.eval_finsetSum, bernsteinPolynomial.sum, Polynomial.eval_one]`.
-/
lemma sum_bern (δ : ℝ) : ∑ T : Finset α, bern δ T = 1 := by
  have h := sum_card (α := α) δ (fun _ => 1)
  simp only [mul_one] at h
  rw [h, ← Polynomial.eval_finsetSum, bernsteinPolynomial.sum, Polynomial.eval_one]

/- English proof (translation)
Establish `h` using `sum_card (α := α) δ (fun k => ((k : ℝ) - δ * Fintype.card α) ^ 2)`. Rewrite using `[h]`. Establish `hv` using `congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance ℝ (Fintype.card α))`. Simplify using `only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_one, nsmul_eq_mul] at hv`. Rewrite using `[← hv]`.

Use `sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sum_bern_var (δ : ℝ) :
    ∑ T : Finset α, bern δ T * ((T.card : ℝ) - δ * Fintype.card α) ^ 2 =
      Fintype.card α * δ * (1 - δ) := by
  have h := sum_card (α := α) δ (fun k => ((k : ℝ) - δ * Fintype.card α) ^ 2)
  rw [h]
  have hv := congrArg (Polynomial.eval δ) (bernsteinPolynomial.variance ℝ (Fintype.card α))
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_natCast,
    Polynomial.eval_one, nsmul_eq_mul] at hv
  rw [← hv]
  refine sum_congr rfl fun k _ => ?_
  ring

end Formalism.FrobeniusOrbits.BernoulliSumsFrobeniusOrbits

namespace Formalism.FrobeniusOrbits

open BernoulliSumsFrobeniusOrbits

open Classical in
/- English proof (translation)
Introduce `α ι _ _ δ β ω BAD hδ hδ1 hβ hω hn hBAD`. Use `set n : ℝ := (Fintype.card α : ℝ) with hn_def`. Use `set M : ℝ := β * δ * n * ∑ p, ω p with hM_def`. Use `set X : Finset α → ℝ := fun T => ∑ p, ω p * ((T.filter (fun t => BAD p t T)).card : ℝ) with hX_def`. Establish `hb0 : ∀ T : Finset α, 0 ≤ bern δ T` using `bern_nonneg hδ.le hδ1`.

Establish `hX0 : ∀ T, 0 ≤ X T` using `fun T => sum_nonneg fun p _ => mul_nonneg (hω p) (Nat.cast_nonneg _)`. Establish `hM0 : 0 ≤ M`. Establish `: 0 ≤ ∑ p, ω p` using `sum_nonneg fun p _ => hω p`. Establish `: 0 ≤ n` using `Nat.cast_nonneg _`. Check the signs of the components of the expression.

Establish `hc : ∀ p (T : Finset α), ((T.filter (fun t => BAD p t T)).card : ℝ) = ∑ t, if t ∈ T ∧ BAD p t T then (1 : ℝ) else 0`. Introduce `p T`. Rewrite using `[Finset.sum_boole]`. Use `congr 2`. Use extensionality with `t`.

Simplify using the standard rewrite rules. Establish `hEX : ∑ T, bern δ T * X T ≤ M`. Combine the equalities or inequalities in the displayed calculation. Use `sum_congr rfl fun T _ => ?_` and prove the remaining obligations. Simplify using `only [X, hc, mul_sum]`.

Use `sum_congr rfl fun p _ => sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> ring`. Use `_ = ∑ p, ∑ t, ω p * ∑ T : Finset α, (if t ∈ T ∧ BAD p t T then bern δ T else 0) := by`. Rewrite using `[sum_comm]`. Use `sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[sum_comm]`. Simplify using `only [mul_sum]`. Use `_ ≤ ∑ p, ∑ _t : α, ω p * (β * δ) := sum_le_sum fun p _ => sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hBAD p t) (hω p)`. Use `_ = M := by`. Simplify using `only [hM_def, hn_def, sum_const, card_univ, nsmul_eq_mul, mul_sum]`.

Use `sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hA : ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) ≤ 1 / 4`. Establish `key : 4 * M * ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) ≤ M`. Rewrite using `[mul_sum]`.

Use `le_trans (sum_le_sum fun T _ => ?_) hEX` and prove the remaining obligations. Use `split_ifs with h`. Use polynomial arithmetic with `[hb0 T]`. Simplify using `only [mul_zero]`. Conclude with `mul_nonneg (hb0 T) (hX0 T)`.

Break down `hM0.lt_or_eq with hpos | hzero` into its components or cases. Use the polynomial consequences of the given equalities and inequalities. Establish `hsum0 : ∑ T, bern δ T * X T = 0` using `le_antisymm (hzero ▸ hEX) (sum_nonneg fun T _ => mul_nonneg (hb0 T) (hX0 T))`. Establish `hall` using `(Finset.sum_eq_zero_iff_of_nonneg (fun T _ => mul_nonneg (hb0 T) (hX0 T))).mp hsum0`. Establish `: ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) = 0`.

Use `sum_eq_zero fun T _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Establish `hXT : 0 < X T` using `by rw [← hzero] at h; linarith`. Use `hall T (mem_univ _)` as an intermediate fact. Break down `mul_eq_zero.mp this with h' | h'` into its components or cases.

Conclude with `h'`. Combine the linear equalities and inequalities to obtain the conclusion. Both sides reduce to the same expression. Rewrite using `[this]`. Evaluate the numerical expressions.

Establish `hB : ∑ T : Finset α, (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) ≤ 1 / 4` using `by set S := ∑ T : Finset α, (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) with hS`. Apply the tactic sequence `have hS0 : 0 ≤ S := sum_nonneg fun T _ => by split_ifs <;> simp [hb0 T]`. Establish `key : (δ * n / 2) ^ 2 * S ≤ δ * n`. Establish `hv` using `sum_bern_var (α := α) δ`. Rewrite using `[hS, mul_sum]`.

Combine the equalities or inequalities in the displayed calculation. Use `sum_le_sum fun T _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Use polynomial arithmetic with `[hb0 T]`. Simplify using `only [mul_zero]`.

Conclude with `mul_nonneg (hb0 T) (sq_nonneg _)`. Use `_ = n * δ * (1 - δ) := hv`. Use `_ ≤ δ * n := by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)]`. Assume the negation of the conclusion as `hlt`. Use `push Not at hlt`.

Establish `hc0 : 0 < δ * n` using `by linarith`. Establish `h1 : (δ * n / 2) ^ 2 * (1 / 4) < (δ * n / 2) ^ 2 * S` using `mul_lt_mul_of_pos_left hlt (by positivity)`. Use polynomial arithmetic with `[hn]`. Assume the negation of the conclusion as `hne`. Use `push Not at hne`.

Establish `hle : ∀ T : Finset α, bern δ T ≤ (if 4 * M < X T then bern δ T else 0) + (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0)`. Introduce `T`. Distinguish the cases in `h2 : (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2`. Apply the tactic sequence `rw [if_pos h2]; split_ifs <;> linarith [hb0 T]`. Rewrite using `[if_neg h2]`.

Establish `hab` using `abs_le_of_sq_le_sq' (not_lt.mp h2) (by positivity)`. Establish `h4 : 4 * M < X T`. Use `hne T (by linarith [hab.1]) (by linarith [hab.2])` as an intermediate fact. Simplify using `only [X, hM_def]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[if_pos h4]`. Combine the linear equalities and inequalities to obtain the conclusion. Use `sum_le_sum fun T (_ : T ∈ (univ : Finset (Finset α))) => hle T` as an intermediate fact. Rewrite `this` using `[sum_add_distrib, sum_bern]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem hostTops : HostTops := by
  intro α ι _ _ δ β ω BAD hδ hδ1 hβ hω hn hBAD
  set n : ℝ := (Fintype.card α : ℝ) with hn_def
  set M : ℝ := β * δ * n * ∑ p, ω p with hM_def
  set X : Finset α → ℝ := fun T => ∑ p, ω p * ((T.filter (fun t => BAD p t T)).card : ℝ)
    with hX_def
  have hb0 : ∀ T : Finset α, 0 ≤ bern δ T := bern_nonneg hδ.le hδ1
  have hX0 : ∀ T, 0 ≤ X T := fun T => sum_nonneg fun p _ => mul_nonneg (hω p) (Nat.cast_nonneg _)
  have hM0 : 0 ≤ M := by
    have : 0 ≤ ∑ p, ω p := sum_nonneg fun p _ => hω p
    have : 0 ≤ n := Nat.cast_nonneg _
    positivity

  have hc : ∀ p (T : Finset α), ((T.filter (fun t => BAD p t T)).card : ℝ) =
      ∑ t, if t ∈ T ∧ BAD p t T then (1 : ℝ) else 0 := by
    intro p T
    rw [Finset.sum_boole]
    congr 2
    ext t
    simp
  have hEX : ∑ T, bern δ T * X T ≤ M := by
    calc ∑ T, bern δ T * X T
        = ∑ T : Finset α, ∑ p, ∑ t, ω p * (if t ∈ T ∧ BAD p t T then bern δ T else 0) := by
          refine sum_congr rfl fun T _ => ?_
          simp only [X, hc, mul_sum]
          refine sum_congr rfl fun p _ => sum_congr rfl fun t _ => ?_
          split_ifs <;> ring
      _ = ∑ p, ∑ t, ω p * ∑ T : Finset α, (if t ∈ T ∧ BAD p t T then bern δ T else 0) := by
          rw [sum_comm]
          refine sum_congr rfl fun p _ => ?_
          rw [sum_comm]
          simp only [mul_sum]
      _ ≤ ∑ p, ∑ _t : α, ω p * (β * δ) :=
          sum_le_sum fun p _ => sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hBAD p t) (hω p)
      _ = M := by
          simp only [hM_def, hn_def, sum_const, card_univ, nsmul_eq_mul, mul_sum]
          refine sum_congr rfl fun p _ => ?_
          ring

  have hA : ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) ≤ 1 / 4 := by
    have key : 4 * M * ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) ≤ M := by
      rw [mul_sum]
      refine le_trans (sum_le_sum fun T _ => ?_) hEX
      split_ifs with h
      · nlinarith [hb0 T]
      · simp only [mul_zero]; exact mul_nonneg (hb0 T) (hX0 T)
    rcases hM0.lt_or_eq with hpos | hzero
    · nlinarith
    · have hsum0 : ∑ T, bern δ T * X T = 0 :=
        le_antisymm (hzero ▸ hEX) (sum_nonneg fun T _ => mul_nonneg (hb0 T) (hX0 T))
      have hall := (Finset.sum_eq_zero_iff_of_nonneg
        (fun T _ => mul_nonneg (hb0 T) (hX0 T))).mp hsum0
      have : ∑ T : Finset α, (if 4 * M < X T then bern δ T else 0) = 0 := by
        refine sum_eq_zero fun T _ => ?_
        split_ifs with h
        · have hXT : 0 < X T := by rw [← hzero] at h; linarith
          have := hall T (mem_univ _)
          rcases mul_eq_zero.mp this with h' | h'
          · exact h'
          · linarith
        · rfl
      rw [this]; norm_num

  have hB : ∑ T : Finset α,
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) ≤ 1 / 4 := by
    set S := ∑ T : Finset α,
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) with hS
    have hS0 : 0 ≤ S := sum_nonneg fun T _ => by split_ifs <;> simp [hb0 T]
    have key : (δ * n / 2) ^ 2 * S ≤ δ * n := by
      have hv := sum_bern_var (α := α) δ
      rw [hS, mul_sum]
      calc ∑ T : Finset α, (δ * n / 2) ^ 2 *
            (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0)
          ≤ ∑ T : Finset α, bern δ T * ((T.card : ℝ) - δ * n) ^ 2 := by
            refine sum_le_sum fun T _ => ?_
            split_ifs with h
            · nlinarith [hb0 T]
            · simp only [mul_zero]; exact mul_nonneg (hb0 T) (sq_nonneg _)
        _ = n * δ * (1 - δ) := hv
        _ ≤ δ * n := by nlinarith [Nat.cast_nonneg (α := ℝ) (Fintype.card α)]
    by_contra hlt
    push Not at hlt
    have hc0 : 0 < δ * n := by linarith
    have h1 : (δ * n / 2) ^ 2 * (1 / 4) < (δ * n / 2) ^ 2 * S :=
      mul_lt_mul_of_pos_left hlt (by positivity)
    nlinarith [hn]

  by_contra hne
  push Not at hne
  have hle : ∀ T : Finset α, bern δ T ≤ (if 4 * M < X T then bern δ T else 0) +
      (if (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2 then bern δ T else 0) := by
    intro T
    by_cases h2 : (δ * n / 2) ^ 2 < ((T.card : ℝ) - δ * n) ^ 2
    · rw [if_pos h2]; split_ifs <;> linarith [hb0 T]
    · rw [if_neg h2]
      have hab := abs_le_of_sq_le_sq' (not_lt.mp h2) (by positivity)
      have h4 : 4 * M < X T := by
        have := hne T (by linarith [hab.1]) (by linarith [hab.2])
        simp only [X, hM_def]
        linarith
      rw [if_pos h4]; linarith
  have := sum_le_sum fun T (_ : T ∈ (univ : Finset (Finset α))) => hle T
  rw [sum_add_distrib, sum_bern] at this
  linarith

end Formalism.FrobeniusOrbits
