import Mathlib
open scoped InnerProductSpace

namespace GlobalTheory

open Set Filter Topology

/- English proof (translation)
Use `set M : ℕ → ℝ := fun n => Real.sqrt (b * a ^ n * n.factorial) with hM`. Establish `base : ∀ k t, ‖φ k t‖ ≤ M k`. Introduce `k t`. Use `Real.abs_le_sqrt (hb k t)` as an intermediate fact. Rewrite `this` using `[abs_of_nonneg (norm_nonneg _)]`. Then use the resulting hypothesis.

Establish `key : ∀ m k, ∀ t ∈ Icc (0:ℝ) 1, ‖φ k t‖ ≤ M (k + m) * t ^ m / m.factorial`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro k t _`. Simplify using `using base k t`.

Consider the case `succ m ih`. Introduce `k`. Establish `hB : ∀ x, HasDerivAt (fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial) (M ((k + 1) + m) * x ^ m / m.factorial) x`. Introduce `x`. Establish `h1` using `((hasDerivAt_pow (m + 1) x).const_mul (M (k + (m + 1)))).div_const ((m + 1).factorial : ℝ)`.

Use `h1.congr_deriv ?_` and prove the remaining obligations. Rewrite using `[show k + 1 + m = k + (m + 1) by ring]`. Simplify using `only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]`. Establish `: (m.factorial : ℝ) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts.

Use `image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ k) (f' := φ (k + 1)) (a := 0) (b := 1) (fun x _ => (hd k x).continuousAt.continuousWithinAt) (fun x _ => (hd k x).hasDerivWithinAt) (B := fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial) (by simp [h0 k]) h …` as an intermediate fact. Conclude with `this`. Establish `hn : ∀ n : ℕ, ‖φ 0 1‖ ^ 2 ≤ b * (a ^ n / n.factorial)`. Introduce `n`. Establish `h` using `key n 0 1 (by simp)`.

Simplify using `only [zero_add, one_pow, mul_one] at h`. Establish `hX : 0 ≤ b * a ^ n * n.factorial` using `le_trans (by positivity) (hb n 1)`. Establish `h2` using `pow_le_pow_left₀ (norm_nonneg _) h 2`. Rewrite `h2` using `[div_pow, hM, Real.sq_sqrt hX]`. Use `h2.trans (le_of_eq ?_)` and prove the remaining obligations.

Establish `: (n.factorial : ℝ) ≠ 0` using `by positivity`. Clear the denominators using the available nonvanishing facts. Establish `ht : Tendsto (fun n : ℕ => b * (a ^ n / n.factorial)) atTop (𝓝 (b * 0))` using `(FloorSemiring.tendsto_pow_div_factorial_atTop a).const_mul b`. Rewrite `ht` using `[mul_zero]`. Establish `hle : ‖φ 0 1‖ ^ 2 ≤ 0` using `ge_of_tendsto' ht hn`.

Establish `: ‖φ 0 1‖ = 0` using `by nlinarith [norm_nonneg (φ 0 1)]`. Conclude with `norm_eq_zero.mp this`.
-/
theorem vanish_at_one_of_derivs_vanish_of_growth (φ : ℕ → ℝ → ℂ) (a b : ℝ)
    (hd : ∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) (h0 : ∀ k, φ k 0 = 0)
    (hb : ∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) : φ 0 1 = 0 := by
  set M : ℕ → ℝ := fun n => Real.sqrt (b * a ^ n * n.factorial) with hM
  have base : ∀ k t, ‖φ k t‖ ≤ M k := by
    intro k t
    have := Real.abs_le_sqrt (hb k t)
    rwa [abs_of_nonneg (norm_nonneg _)] at this
  have key : ∀ m k, ∀ t ∈ Icc (0:ℝ) 1, ‖φ k t‖ ≤ M (k + m) * t ^ m / m.factorial := by
    intro m
    induction m with
    | zero => intro k t _; simpa using base k t
    | succ m ih =>
      intro k
      have hB : ∀ x, HasDerivAt (fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial)
          (M ((k + 1) + m) * x ^ m / m.factorial) x := by
        intro x
        have h1 := ((hasDerivAt_pow (m + 1) x).const_mul (M (k + (m + 1)))).div_const
          ((m + 1).factorial : ℝ)
        refine h1.congr_deriv ?_
        rw [show k + 1 + m = k + (m + 1) by ring]
        simp only [Nat.factorial_succ, Nat.cast_mul, Nat.add_sub_cancel]
        have : (m.factorial : ℝ) ≠ 0 := by positivity
        field_simp
      have := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := φ k)
        (f' := φ (k + 1)) (a := 0) (b := 1)
        (fun x _ => (hd k x).continuousAt.continuousWithinAt)
        (fun x _ => (hd k x).hasDerivWithinAt)
        (B := fun t : ℝ => M (k + (m + 1)) * t ^ (m + 1) / (m + 1).factorial)
        (by simp [h0 k]) hB
        (fun x hx => ih (k + 1) x (Ico_subset_Icc_self hx))
      exact this
  have hn : ∀ n : ℕ, ‖φ 0 1‖ ^ 2 ≤ b * (a ^ n / n.factorial) := by
    intro n
    have h := key n 0 1 (by simp)
    simp only [zero_add, one_pow, mul_one] at h
    have hX : 0 ≤ b * a ^ n * n.factorial := le_trans (by positivity) (hb n 1)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    rw [div_pow, hM, Real.sq_sqrt hX] at h2
    refine h2.trans (le_of_eq ?_)
    have : (n.factorial : ℝ) ≠ 0 := by positivity
    field_simp
  have ht : Tendsto (fun n : ℕ => b * (a ^ n / n.factorial)) atTop (𝓝 (b * 0)) :=
    (FloorSemiring.tendsto_pow_div_factorial_atTop a).const_mul b
  rw [mul_zero] at ht
  have hle : ‖φ 0 1‖ ^ 2 ≤ 0 := ge_of_tendsto' ht hn
  have : ‖φ 0 1‖ = 0 := by nlinarith [norm_nonneg (φ 0 1)]
  exact norm_eq_zero.mp this

/- English proof (translation)
The claim follows from `vanish_at_one_of_derivs_vanish_of_growth`.
-/
example : ∀ (φ : ℕ → ℝ → ℂ) (a b : ℝ), (∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) → (∀ k, φ k 0 = 0) → (∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) → φ 0 1 = 0 :=
  vanish_at_one_of_derivs_vanish_of_growth

end GlobalTheory
