import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ g a ρ d hρ ha hle hlt`. Establish `hsub : ∀ x y : K, ‖x - y‖ ≤ max ‖x‖ ‖y‖`. Introduce `x y`. Simplify `IsUltrametricDist.norm_add_le_max x (-y)` using `[sub_eq_add_neg, norm_neg]`. Establish `hcoef : ∀ k, ((X - C a) * g).coeff (k + 1) = g.coeff k - g.coeff (k + 1) * a`.

Introduce `k`. Rewrite using `[mul_comm]`. Conclude with `coeff_mul_X_sub_C`. Establish `hcoef0 : ((X - C a) * g).coeff 0 = -a * g.coeff 0`. Rewrite using `[mul_coeff_zero]`.

Simplify using the standard rewrite rules. Establish `hM : 0 < ‖g.coeff d‖ * ρ ^ d`. Establish `h` using `hlt (d + 1) (Nat.lt_succ_self d)`. Establish `: 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hsmall : ‖g.coeff (d + 1) * a‖ < ‖g.coeff d‖`. Rewrite using `[norm_mul]`. Establish `hp : 0 < ρ ^ (d + 1)` using `by positivity`. Establish `h` using `hlt (d + 1) (Nat.lt_succ_self d)`. Establish `hn : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1)` using `by positivity`.

Establish `h2 : ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1) < ‖g.coeff d‖ * ρ ^ (d + 1)`. Combine the equalities or inequalities in the displayed calculation. Conclude with `lt_of_mul_lt_mul_right h2 hp.le`. Establish `htopn : ‖((X - C a) * g).coeff (d + 1)‖ = ‖g.coeff d‖`. Rewrite using `[hcoef d, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hsmall.ne'), norm_neg]`.

Conclude with `max_eq_left hsmall.le`. Establish `htop : ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) = ρ * (‖g.coeff d‖ * ρ ^ d)`. Rewrite using `[htopn]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ k, ‖((X - C a) * g).coeff (k + 1)‖ * ρ ^ (k + 1) ≤ max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)))`.

Introduce `k`. Rewrite using `[hcoef k]`. Establish `h1` using `hsub (g.coeff k) (g.coeff (k + 1) * a)`. Rewrite `h1` using `[norm_mul]`. Establish `hp : 0 ≤ ρ ^ (k + 1)` using `by positivity`.

Establish `hn : 0 ≤ ‖g.coeff (k + 1)‖ * ρ ^ (k + 1)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation. Apply `max_le_max` to reduce the goal to its premises. Conclude with `le_of_eq (by ring)`. Combine the equalities or inequalities in the displayed calculation.

Prove the components needed by the constructor for the conclusion. Introduce `j`. Rewrite using `[htop]`. Consider the cases of `j with`. Consider the case `zero`.

Rewrite using `[hcoef0, norm_mul, norm_neg, pow_zero, mul_one]`. Establish `h0` using `hle 0`. Rewrite `h0` using `[pow_zero, mul_one]`. Combine the equalities or inequalities in the displayed calculation. Consider the case `succ k`.

Conclude with `(key k).trans (max_le (mul_le_mul_of_nonneg_left (hle k) hρ.le) (mul_le_mul_of_nonneg_left (hle (k + 1)) hρ.le))`. Introduce `j hj`. Rewrite using `[htop]`. Take `⟨k, rfl⟩ : ∃ k, j = k + 1` from `⟨j - 1, by omega⟩`. Conclude with `(key k).trans_lt (max_lt (mul_lt_mul_of_pos_left (hlt k (by omega)) hρ) (mul_lt_mul_of_pos_left (hlt (k + 1) (by omega)) hρ))`.
-/
theorem newton_step_root_in_disc :
    ∀ (K : Type) [NormedField K] [IsUltrametricDist K] (g : K[X]) (a : K) (ρ : ℝ) (d : ℕ),
      0 < ρ → ‖a‖ ≤ ρ → (∀ j, ‖g.coeff j‖ * ρ ^ j ≤ ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, d < j → ‖g.coeff j‖ * ρ ^ j < ‖g.coeff d‖ * ρ ^ d) →
      (∀ j, ‖((X - C a) * g).coeff j‖ * ρ ^ j ≤ ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1)) ∧
        ∀ j, d + 1 < j → ‖((X - C a) * g).coeff j‖ * ρ ^ j <
          ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) := by
  intro K _ _ g a ρ d hρ ha hle hlt
  have hsub : ∀ x y : K, ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
    intro x y
    simpa [sub_eq_add_neg, norm_neg] using IsUltrametricDist.norm_add_le_max x (-y)
  have hcoef : ∀ k, ((X - C a) * g).coeff (k + 1) = g.coeff k - g.coeff (k + 1) * a := by
    intro k
    rw [mul_comm]
    exact coeff_mul_X_sub_C
  have hcoef0 : ((X - C a) * g).coeff 0 = -a * g.coeff 0 := by
    rw [mul_coeff_zero]
    simp

  have hM : 0 < ‖g.coeff d‖ * ρ ^ d := by
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    linarith
  have hsmall : ‖g.coeff (d + 1) * a‖ < ‖g.coeff d‖ := by
    rw [norm_mul]
    have hp : 0 < ρ ^ (d + 1) := by positivity
    have h := hlt (d + 1) (Nat.lt_succ_self d)
    have hn : 0 ≤ ‖g.coeff (d + 1)‖ * ρ ^ (d + 1) := by positivity
    have h2 : ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1) < ‖g.coeff d‖ * ρ ^ (d + 1) := by
      calc ‖g.coeff (d + 1)‖ * ‖a‖ * ρ ^ (d + 1)
          = (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ‖a‖ := by ring
        _ ≤ (‖g.coeff (d + 1)‖ * ρ ^ (d + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
        _ < (‖g.coeff d‖ * ρ ^ d) * ρ := mul_lt_mul_of_pos_right h hρ
        _ = ‖g.coeff d‖ * ρ ^ (d + 1) := by ring
    exact lt_of_mul_lt_mul_right h2 hp.le
  have htopn : ‖((X - C a) * g).coeff (d + 1)‖ = ‖g.coeff d‖ := by
    rw [hcoef d, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg]; exact hsmall.ne'),
      norm_neg]
    exact max_eq_left hsmall.le
  have htop : ‖((X - C a) * g).coeff (d + 1)‖ * ρ ^ (d + 1) = ρ * (‖g.coeff d‖ * ρ ^ d) := by
    rw [htopn]; ring

  have key : ∀ k, ‖((X - C a) * g).coeff (k + 1)‖ * ρ ^ (k + 1) ≤
      max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
    intro k
    rw [hcoef k]
    have h1 := hsub (g.coeff k) (g.coeff (k + 1) * a)
    rw [norm_mul] at h1
    have hp : 0 ≤ ρ ^ (k + 1) := by positivity
    have hn : 0 ≤ ‖g.coeff (k + 1)‖ * ρ ^ (k + 1) := by positivity
    calc ‖g.coeff k - g.coeff (k + 1) * a‖ * ρ ^ (k + 1)
        ≤ max ‖g.coeff k‖ (‖g.coeff (k + 1)‖ * ‖a‖) * ρ ^ (k + 1) :=
          mul_le_mul_of_nonneg_right h1 hp
      _ = max (‖g.coeff k‖ * ρ ^ (k + 1)) (‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)) :=
          max_mul_of_nonneg _ _ hp
      _ ≤ max (ρ * (‖g.coeff k‖ * ρ ^ k)) (ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1))) := by
          apply max_le_max
          · exact le_of_eq (by ring)
          · calc ‖g.coeff (k + 1)‖ * ‖a‖ * ρ ^ (k + 1)
                = (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ‖a‖ := by ring
              _ ≤ (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) * ρ := mul_le_mul_of_nonneg_left ha hn
              _ = ρ * (‖g.coeff (k + 1)‖ * ρ ^ (k + 1)) := by ring
  constructor
  · intro j
    rw [htop]
    cases j with
    | zero =>
      rw [hcoef0, norm_mul, norm_neg, pow_zero, mul_one]
      have h0 := hle 0
      rw [pow_zero, mul_one] at h0
      calc ‖a‖ * ‖g.coeff 0‖ ≤ ρ * ‖g.coeff 0‖ :=
            mul_le_mul_of_nonneg_right ha (norm_nonneg _)
        _ ≤ ρ * (‖g.coeff d‖ * ρ ^ d) := mul_le_mul_of_nonneg_left h0 hρ.le
    | succ k =>
      exact (key k).trans (max_le (mul_le_mul_of_nonneg_left (hle k) hρ.le)
        (mul_le_mul_of_nonneg_left (hle (k + 1)) hρ.le))
  · intro j hj
    rw [htop]
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    exact (key k).trans_lt (max_lt (mul_lt_mul_of_pos_left (hlt k (by omega)) hρ)
      (mul_lt_mul_of_pos_left (hlt (k + 1) (by omega)) hρ))

end GlobalTheory
