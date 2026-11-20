import ReciprocityTheory.GeometryOfNumbers.AsymptoticSequences.DefectSt
import Mathlib

namespace ReciprocityTheory.GeometryOfNumbersTheory

open Filter Topology Asymptotics

/- English proof (translation)
Unfold `hsDefect`. Use `push_cast`. Rewrite using `[mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hsDefect_two_mul (D : ℕ) (hh : ℝ) (n : ℕ) :
    hsDefect D (fun m => chiP D (2 * m)) (2 ^ (D + 1) * hh) n = hsDefect D (chiP D) hh (2 * n) := by
  unfold hsDefect
  push_cast
  rw [mul_pow]
  ring

/- English proof (translation)
Take `⟨N1, hN1⟩` from `eventually_atTop.1 h1`. Take `⟨N2, hN2⟩` from `eventually_atTop.1 h2`. Take `⟨N3, hN3⟩` from `eventually_atTop.1 hf`. Establish `hp : (1 : ℝ) ≤ 2 ^ D` using `one_le_pow₀ (by norm_num)`. Establish `hp0 : (0 : ℝ) < 2 ^ D` using `by positivity`.

Establish `hev : ∀ n : ℕ, N1 + N2 + N3 ≤ n → |f (2 * n)| ≤ 2 ^ D * A * (n : ℝ) ^ (D + 1) + δ * (n : ℝ) ^ (D + 1)`. Introduce `n hn`. Establish `e1` using `hN1 n (by omega)`. Establish `e3` using `hN3 n (by omega)`. Establish `h0` using `abs_sub_abs_le_abs_sub (f (2 * n)) (2 ^ D * f n)`.

Rewrite `h0` using `[abs_mul, abs_of_pos hp0]`. Establish `hpA : 2 ^ D * |f n| ≤ 2 ^ D * (A * (n : ℝ) ^ (D + 1))` using `mul_le_mul_of_nonneg_left e3 hp0.le`. Use the polynomial consequences of the given equalities and inequalities. Establish `hcast : ∀ n : ℕ, (((2 * n : ℕ) : ℝ)) ^ (D + 1) = 2 * 2 ^ D * (n : ℝ) ^ (D + 1)`. Introduce `n`.

Use `push_cast`. Rewrite using `[mul_pow, pow_succ]`. Expand and normalize the polynomial expressions, which then agree. Use `eventually_atTop.2 ⟨2 * (N1 + N2 + N3) + 1, fun m hm => ?_⟩` and prove the remaining obligations. Take `⟨n, rfl | rfl⟩` from `Nat.even_or_odd' m`.

Establish `hn : N1 + N2 + N3 ≤ n` using `by omega`. Establish `hx : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1)` using `by positivity`. Establish `e` using `hev n hn`. Rewrite using `[hcast]`. Establish `hδx : δ * (n : ℝ) ^ (D + 1) * 1 ≤ δ * (n : ℝ) ^ (D + 1) * 2 ^ D` using `mul_le_mul_of_nonneg_left hp (mul_nonneg hδ.le hx)`.

Use the polynomial consequences of the given equalities and inequalities. Establish `hn : N1 + N2 + N3 ≤ n` using `by omega`. Establish `hx : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1)` using `by positivity`. Establish `e` using `hev n hn`. Establish `e2` using `hN2 (2 * n) (by omega)`.

Rewrite `e2` using `[hcast]`. Establish `h0` using `abs_sub_abs_le_abs_sub (f (2 * n + 1)) (f (2 * n))`. Establish `hmono : (((2 * n : ℕ) : ℝ)) ^ (D + 1) ≤ (((2 * n + 1 : ℕ) : ℝ)) ^ (D + 1)`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises. Conclude with `Nat.le_succ _` after adjusting the coercions.

Rewrite `hmono` using `[hcast]`. Establish `hco : 0 ≤ A / 2 + 2 * δ` using `by positivity`. Establish `h3` using `mul_le_mul_of_nonneg_left hmono hco`. Establish `hδx : δ * (n : ℝ) ^ (D + 1) * 1 ≤ δ * (n : ℝ) ^ (D + 1) * 2 ^ D` using `mul_le_mul_of_nonneg_left hp (mul_nonneg hδ.le hx)`. Use the polynomial consequences of the given equalities and inequalities.
-/
private theorem eventually_abs_le_half_add_of_doubling_bounds (D : ℕ) (f : ℕ → ℝ) (A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ)
    (h1 : ∀ᶠ n : ℕ in atTop, |f (2 * n) - 2 ^ D * f n| ≤ δ * (n : ℝ) ^ (D + 1))
    (h2 : ∀ᶠ n : ℕ in atTop, |f (n + 1) - f n| ≤ δ * (n : ℝ) ^ (D + 1))
    (hf : ∀ᶠ n : ℕ in atTop, |f n| ≤ A * (n : ℝ) ^ (D + 1)) :
    ∀ᶠ n : ℕ in atTop, |f n| ≤ (A / 2 + 2 * δ) * (n : ℝ) ^ (D + 1) := by
  obtain ⟨N1, hN1⟩ := eventually_atTop.1 h1
  obtain ⟨N2, hN2⟩ := eventually_atTop.1 h2
  obtain ⟨N3, hN3⟩ := eventually_atTop.1 hf
  have hp : (1 : ℝ) ≤ 2 ^ D := one_le_pow₀ (by norm_num)
  have hp0 : (0 : ℝ) < 2 ^ D := by positivity

  have hev : ∀ n : ℕ, N1 + N2 + N3 ≤ n →
      |f (2 * n)| ≤ 2 ^ D * A * (n : ℝ) ^ (D + 1) + δ * (n : ℝ) ^ (D + 1) := by
    intro n hn
    have e1 := hN1 n (by omega)
    have e3 := hN3 n (by omega)
    have h0 := abs_sub_abs_le_abs_sub (f (2 * n)) (2 ^ D * f n)
    rw [abs_mul, abs_of_pos hp0] at h0
    have hpA : 2 ^ D * |f n| ≤ 2 ^ D * (A * (n : ℝ) ^ (D + 1)) :=
      mul_le_mul_of_nonneg_left e3 hp0.le
    nlinarith
  have hcast : ∀ n : ℕ, (((2 * n : ℕ) : ℝ)) ^ (D + 1) = 2 * 2 ^ D * (n : ℝ) ^ (D + 1) := by
    intro n
    push_cast
    rw [mul_pow, pow_succ]
    ring
  refine eventually_atTop.2 ⟨2 * (N1 + N2 + N3) + 1, fun m hm => ?_⟩
  obtain ⟨n, rfl | rfl⟩ := Nat.even_or_odd' m
  · have hn : N1 + N2 + N3 ≤ n := by omega
    have hx : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
    have e := hev n hn
    rw [hcast]
    have hδx : δ * (n : ℝ) ^ (D + 1) * 1 ≤ δ * (n : ℝ) ^ (D + 1) * 2 ^ D :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hδ.le hx)
    nlinarith
  · have hn : N1 + N2 + N3 ≤ n := by omega
    have hx : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1) := by positivity
    have e := hev n hn
    have e2 := hN2 (2 * n) (by omega)
    rw [hcast] at e2
    have h0 := abs_sub_abs_le_abs_sub (f (2 * n + 1)) (f (2 * n))
    have hmono : (((2 * n : ℕ) : ℝ)) ^ (D + 1) ≤ (((2 * n + 1 : ℕ) : ℝ)) ^ (D + 1) := by
      apply pow_le_pow_left₀ (by positivity)
      exact_mod_cast Nat.le_succ _
    rw [hcast] at hmono
    have hco : 0 ≤ A / 2 + 2 * δ := by positivity
    have h3 := mul_le_mul_of_nonneg_left hmono hco
    have hδx : δ * (n : ℝ) ^ (D + 1) * 1 ≤ δ * (n : ℝ) ^ (D + 1) * 2 ^ D :=
      mul_le_mul_of_nonneg_left hp (mul_nonneg hδ.le hx)
    nlinarith

/- English proof (translation)
Establish `hC' : ∀ n : ℕ, |f n| ≤ |C| * (n : ℝ) ^ (D + 1)` using `fun n => (hC n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))`. Rewrite using `[Asymptotics.isLittleO_iff]`. Introduce `c hc`. Establish `key : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop, |f n| ≤ (|C| / 2 ^ k + 2 * (c / 3)) * (n : ℝ) ^ (D + 1)`. Introduce `k`.

Proceed by induction on `k with`. Consider the case `zero`. Use `Eventually.of_forall fun n => (hC' n).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))` and prove the remaining obligations. Rewrite using `[pow_zero, div_one]`. Combine the linear equalities and inequalities to obtain the conclusion.

Consider the case `succ k ih`. Use `eventually_abs_le_half_add_of_doubling_bounds D f _ (c / 3 / 2) (by positivity) (by positivity) (h1 _ (by positivity)) (h2 _ (by positivity)) ih` as an intermediate fact. Use `this.mono fun n hn => hn.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[pow_succ]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨k, hk⟩` from `pow_unbounded_of_one_lt (|C| * 3 / c) (by norm_num : (1 : ℝ) < 2)`. Establish `h2k : (0 : ℝ) < 2 ^ k` using `by positivity`. Rewrite `hk` using `[div_lt_iff₀ hc]`. Establish `hsmall : |C| / 2 ^ k ≤ c / 3`. Rewrite using `[div_le_iff₀ h2k]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `(key k).mono fun n hn => ?_` and prove the remaining obligations. Rewrite using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]`. Use `hn.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))` and prove the remaining obligations. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem isLittleO_pow_of_doubling_and_increment_bounds (D : ℕ) (f : ℕ → ℝ) (C : ℝ)
    (hC : ∀ n : ℕ, |f n| ≤ C * (n : ℝ) ^ (D + 1))
    (h1 : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, |f (2 * n) - 2 ^ D * f n| ≤ δ * (n : ℝ) ^ (D + 1))
    (h2 : ∀ δ > 0, ∀ᶠ n : ℕ in atTop, |f (n + 1) - f n| ≤ δ * (n : ℝ) ^ (D + 1)) :
    f =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  have hC' : ∀ n : ℕ, |f n| ≤ |C| * (n : ℝ) ^ (D + 1) := fun n =>
    (hC n).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  rw [Asymptotics.isLittleO_iff]
  intro c hc
  have key : ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
      |f n| ≤ (|C| / 2 ^ k + 2 * (c / 3)) * (n : ℝ) ^ (D + 1) := by
    intro k
    induction k with
    | zero =>
      refine Eventually.of_forall fun n => (hC' n).trans
        (mul_le_mul_of_nonneg_right ?_ (by positivity))
      rw [pow_zero, div_one]
      linarith
    | succ k ih =>
      have := eventually_abs_le_half_add_of_doubling_bounds D f _ (c / 3 / 2) (by positivity) (by positivity)
        (h1 _ (by positivity)) (h2 _ (by positivity)) ih
      refine this.mono fun n hn => hn.trans (le_of_eq ?_)
      rw [pow_succ]
      ring
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (|C| * 3 / c) (by norm_num : (1 : ℝ) < 2)
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  rw [div_lt_iff₀ hc] at hk
  have hsmall : |C| / 2 ^ k ≤ c / 3 := by
    rw [div_le_iff₀ h2k]
    linarith
  refine (key k).mono fun n hn => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]
  refine hn.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
  linarith

/- English proof (translation)
Take `⟨C, hC⟩` from `hilbertSamuelDefect_projectiveSpace_abs_le D hh`. Use `isLittleO_pow_of_doubling_and_increment_bounds D _ C hC (fun δ hδ => ?_) (fun δ hδ => ?_)` and prove the remaining obligations. Use `(hver.def hδ).mono fun n hn => ?_` and prove the remaining obligations. Rewrite `hn` using `[Real.norm_eq_abs, Real.norm_eq_abs, hsDefect_two_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]`. Then use the resulting hypothesis. Use `((hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO D hh).def hδ).mono fun n hn => ?_` and prove the remaining obligations.

Rewrite `hn` using `[Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))]`. Then use the resulting hypothesis.
-/
theorem hilbertSamuelDefect_projectiveSpace_isLittleO (D : ℕ) (hh : ℝ)
    (hver : (fun n => hsDefect D (fun m => chiP D (2 * m)) (2 ^ (D + 1) * hh) n -
      2 ^ D * hsDefect D (chiP D) hh n) =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1)) :
    hsDefect D (chiP D) hh =o[atTop] fun n : ℕ => (n : ℝ) ^ (D + 1) := by
  obtain ⟨C, hC⟩ := hilbertSamuelDefect_projectiveSpace_abs_le D hh
  refine isLittleO_pow_of_doubling_and_increment_bounds D _ C hC (fun δ hδ => ?_) (fun δ hδ => ?_)
  · refine (hver.def hδ).mono fun n hn => ?_
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, hsDefect_two_mul,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))] at hn
  · refine ((hilbertSamuelDefect_projectiveSpace_succ_sub_isLittleO D hh).def hδ).mono fun n hn => ?_
    rwa [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ (D + 1))] at hn

end ReciprocityTheory.GeometryOfNumbersTheory
