import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Imports
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff

open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam

namespace GlobalTheory.ThZero

/- English proof (translation)
Simplify using `only [ee, mul_add, Complex.exp_add]`.
-/
lemma ee_add (a b : ℂ) : ee (a + b) = ee a * ee b := by
  simp only [ee, mul_add, Complex.exp_add]

/- English proof (translation)
The claim follows from `Complex.exp_ne_zero _`.
-/
lemma ee_ne (a : ℂ) : ee a ≠ 0 := Complex.exp_ne_zero _

/- English proof (translation)
Simplify using `only [ee, mul_neg, Complex.exp_neg]`.
-/
lemma ee_neg (a : ℂ) : ee (-a) = (ee a)⁻¹ := by
  simp only [ee, mul_neg, Complex.exp_neg]

/- English proof (translation)
Simplify using `only [ee]`. Rewrite using `[← Complex.exp_nat_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ee_pow (a : ℂ) (n : ℕ) : ee a ^ n = ee ((n : ℂ) * a) := by
  simp only [ee]
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/- English proof (translation)
Establish `h : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0` using `Complex.two_pi_I_ne_zero`. Simplify using `only [ee, Complex.exp_eq_one_iff]`. Use `exists_congr fun k => ⟨fun hk => ?_, fun hk => ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ h` to reduce the goal to its premises. Rewrite using `[hk]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hk]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma ee_eq_one_iff (a : ℂ) : ee a = 1 ↔ ∃ k : ℤ, a = k := by
  have h : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  simp only [ee, Complex.exp_eq_one_iff]
  refine exists_congr fun k => ⟨fun hk => ?_, fun hk => ?_⟩
  · apply mul_left_cancel₀ h
    rw [hk]; ring
  · rw [hk]; ring

/- English proof (translation)
Simplify using `only [ee, Complex.norm_exp]`. Rewrite using `[Real.exp_lt_one_iff]`. Establish `h1` using `τ.im_pos`. Establish `h2` using `Real.pi_pos`. Establish `: (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im)`.

Simplify using the standard rewrite rules. Rewrite using `[this]`. Establish `: 0 < 2 * Real.pi * τ.im` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma norm_ee_lt_one (τ : ℍ) : ‖ee (τ : ℂ)‖ < 1 := by
  simp only [ee, Complex.norm_exp]
  rw [Real.exp_lt_one_iff]
  have h1 := τ.im_pos
  have h2 := Real.pi_pos
  have : (2 * (Real.pi : ℂ) * Complex.I * (τ : ℂ)).re = -(2 * Real.pi * τ.im) := by
    simp
  rw [this]
  have : 0 < 2 * Real.pi * τ.im := by positivity
  linarith

/- English proof (translation)
Establish `h` using `summable_geometric_of_lt_one (norm_nonneg _) (norm_ee_lt_one τ)`. Use `(h.mul_right (‖ee (τ : ℂ)‖ * ‖c‖)).congr fun n => ?_` and prove the remaining obligations. Simplify using `only [norm_neg, norm_mul, norm_pow, pow_succ]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma summable_nine_pow_mul_inv_sq_succ (τ : ℍ) (c : ℂ) : Summable fun n : ℕ => ‖-(ee (τ : ℂ) ^ (n + 1) * c)‖ := by
  have h := summable_geometric_of_lt_one (norm_nonneg _) (norm_ee_lt_one τ)
  refine (h.mul_right (‖ee (τ : ℂ)‖ * ‖c‖)).congr fun n => ?_
  simp only [norm_neg, norm_mul, norm_pow, pow_succ]
  ring

/- English proof (translation)
Simplify using `only [sub_eq_add_neg] at ha hb ⊢`. Rewrite using `[(multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ a)).tprod_mul (multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ b))]`. Conclude with `mul_ne_zero (tprod_one_add_ne_zero_of_summable ha (summable_nine_pow_mul_inv_sq_succ τ a)) (tprod_one_add_ne_zero_of_summable hb (summable_nine_pow_mul_inv_sq_succ τ b))`.
-/
lemma tprod_ne (τ : ℍ) (a b : ℂ) (ha : ∀ n : ℕ, 1 - ee (τ : ℂ) ^ (n + 1) * a ≠ 0)
    (hb : ∀ n : ℕ, 1 - ee (τ : ℂ) ^ (n + 1) * b ≠ 0) :
    ∏' n : ℕ, (1 - ee (τ : ℂ) ^ (n + 1) * a) * (1 - ee (τ : ℂ) ^ (n + 1) * b) ≠ 0 := by
  simp only [sub_eq_add_neg] at ha hb ⊢
  rw [(multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ a)).tprod_mul
    (multipliable_one_add_of_summable (summable_nine_pow_mul_inv_sq_succ τ b))]
  exact mul_ne_zero (tprod_one_add_ne_zero_of_summable ha (summable_nine_pow_mul_inv_sq_succ τ a))
    (tprod_one_add_ne_zero_of_summable hb (summable_nine_pow_mul_inv_sq_succ τ b))

/- English proof (translation)
Rewrite using `[← ee_eq_one_iff, sub_eq_zero]`. Establish `h1 : ee z = ee (z / 2) * ee (z / 2)` using `by rw [← ee_add]; congr 1; ring`. Establish `h2 : ee (-z / 2) = (ee (z / 2))⁻¹` using `by rw [← ee_neg]; congr 1; ring`. Rewrite using `[h1, h2]`. Establish `h3` using `ee_ne (z / 2)`.

Prove the components needed by the constructor for the conclusion. Introduce `h nth_rewrite 2 [h]`. Conclude with `mul_inv_cancel₀ h3`. Introduce `h`. Conclude with `eq_inv_of_mul_eq_one_left h`.
-/
lemma first_iff (z : ℂ) : ee (z / 2) - ee (-z / 2) = 0 ↔ ∃ k : ℤ, z = k := by
  rw [← ee_eq_one_iff, sub_eq_zero]
  have h1 : ee z = ee (z / 2) * ee (z / 2) := by rw [← ee_add]; congr 1; ring
  have h2 : ee (-z / 2) = (ee (z / 2))⁻¹ := by rw [← ee_neg]; congr 1; ring
  rw [h1, h2]
  have h3 := ee_ne (z / 2)
  constructor
  · intro h
    nth_rewrite 2 [h]
    exact mul_inv_cancel₀ h3
  · intro h
    exact eq_inv_of_mul_eq_one_left h

/- English proof (translation)
Rewrite using `[ee_pow, ← ee_add, sub_eq_zero, eq_comm, ee_eq_one_iff]`. Use `push_cast`. Both sides reduce to the same expression.
-/
lemma fac_iff (τ : ℍ) (w : ℂ) (n : ℕ) :
    1 - ee (τ : ℂ) ^ (n + 1) * ee w = 0 ↔ ∃ k : ℤ, ((n : ℂ) + 1) * τ + w = k := by
  rw [ee_pow, ← ee_add, sub_eq_zero, eq_comm, ee_eq_one_iff]
  push_cast
  rfl

/- English proof (translation)
Introduce `τ z`. Unfold `th`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Assume the negation of the conclusion as `hne`.

Use `(mul_ne_zero (mul_ne_zero (ee_ne _) ?_) (tprod_ne τ _ _ ?_ ?_)) h` and prove the remaining obligations. Rewrite using `[Ne, first_iff]`. Introduce and unpack `⟨k, hk⟩`. Conclude with `hne ⟨0, k, by simp [hk]⟩`. Introduce `n`.

Rewrite using `[Ne, fac_iff]`. Introduce and unpack `⟨k, hk⟩`. Conclude with `hne ⟨-((n : ℤ) + 1), k, by push_cast; linear_combination hk⟩`. Introduce `n`. Rewrite using `[← ee_neg, Ne, fac_iff]`.

Introduce and unpack `⟨k, hk⟩`. Conclude with `hne ⟨(n : ℤ) + 1, -k, by push_cast; linear_combination -hk⟩`. Introduce and unpack `⟨m, k, hz⟩`. Break down `lt_trichotomy m 0 with hm | hm | hm` into its components or cases. Take `⟨n, rfl⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1)` from `⟨(-m - 1).toNat, by omega⟩`.

Establish `: 1 - ee (τ : ℂ) ^ (n + 1) * ee z = 0` using `(fac_iff τ z n).2 ⟨k, by rw [hz]; push_cast; ring⟩`. Rewrite using `[tprod_of_exists_eq_zero ⟨n, by rw [this, zero_mul]⟩, mul_zero]`. Establish `: ee (z / 2) - ee (-z / 2) = 0` using `(first_iff z).2 ⟨k, by simp [hz, hm]⟩`. Rewrite using `[this, mul_zero, zero_mul]`. Take `⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 1` from `⟨(m - 1).toNat, by omega⟩`.

Establish `: 1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹ = 0`. Rewrite using `[← ee_neg]`. Conclude with `(fac_iff τ (-z) n).2 ⟨-k, by rw [hz]; push_cast; ring⟩`. Rewrite using `[tprod_of_exists_eq_zero ⟨n, by rw [this, mul_zero]⟩, mul_zero]`.
-/
theorem th_eq_zero_iff :
    ∀ (τ : ℍ) (z : ℂ), th z τ = 0 ↔ ∃ m n : ℤ, z = (m : ℂ) * (τ : ℂ) + n := by
  intro τ z
  unfold th
  constructor
  · intro h
    by_contra hne
    refine (mul_ne_zero (mul_ne_zero (ee_ne _) ?_) (tprod_ne τ _ _ ?_ ?_)) h
    · rw [Ne, first_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨0, k, by simp [hk]⟩
    · intro n
      rw [Ne, fac_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨-((n : ℤ) + 1), k, by push_cast; linear_combination hk⟩
    · intro n
      rw [← ee_neg, Ne, fac_iff]
      rintro ⟨k, hk⟩
      exact hne ⟨(n : ℤ) + 1, -k, by push_cast; linear_combination -hk⟩
  · rintro ⟨m, k, hz⟩
    rcases lt_trichotomy m 0 with hm | hm | hm
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = -((n : ℤ) + 1) := ⟨(-m - 1).toNat, by omega⟩
      have : 1 - ee (τ : ℂ) ^ (n + 1) * ee z = 0 :=
        (fac_iff τ z n).2 ⟨k, by rw [hz]; push_cast; ring⟩
      rw [tprod_of_exists_eq_zero ⟨n, by rw [this, zero_mul]⟩, mul_zero]
    · have : ee (z / 2) - ee (-z / 2) = 0 := (first_iff z).2 ⟨k, by simp [hz, hm]⟩
      rw [this, mul_zero, zero_mul]
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, m = (n : ℤ) + 1 := ⟨(m - 1).toNat, by omega⟩
      have : 1 - ee (τ : ℂ) ^ (n + 1) * (ee z)⁻¹ = 0 := by
        rw [← ee_neg]
        exact (fac_iff τ (-z) n).2 ⟨-k, by rw [hz]; push_cast; ring⟩
      rw [tprod_of_exists_eq_zero ⟨n, by rw [this, mul_zero]⟩, mul_zero]

end GlobalTheory.ThZero
