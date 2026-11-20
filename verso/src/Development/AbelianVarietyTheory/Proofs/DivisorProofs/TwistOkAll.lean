import Mathlib

open IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `A _ I _ τ hτ h2 hI a t₀ ha hτa ht₀ hclose`. Use `set c := t₀ * τ t₀ with hc_def`. Establish `hc : IsUnit c` using `ht₀.mul (ht₀.map τ)`. Establish `hτc : τ c = c`. Simplify using `only [hc_def, map_mul, hτ]`.

Expand and normalize the polynomial expressions, which then agree. Take `⟨w, hw⟩` from `hc.exists_right_inv`. Establish `hτw : τ w = w`. Apply `hc.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[hw, ← hτc, ← map_mul, hw, map_one]`.

Use `set b := a * w with hb_def`. Establish `hτb : τ b = b` using `by simp only [hb_def, map_mul, hτa, hτw]`. Establish `hb1 : 1 - b ∈ I`. Establish `: 1 - b = w * (c - a)`. Rewrite using `[hb_def]`.

Take the linear combination `(-1 : A) * hw`. Rewrite using `[this]`. Conclude with `I.mul_mem_left w hclose`. Take `⟨s, hs, hs1⟩` from `HenselianRing.is_henselian (I := I) (X ^ 2 - C b) (monic_X_pow_sub_C b (by norm_num)) 1 (by simpa using hb1) (by`. Establish `: (derivative (X ^ 2 - C b)).eval (1 : A) = 2` using `by simp [one_add_one_eq_two]`.

Rewrite using `[this]`. Conclude with `h2.map _)`. Establish `hs2 : s ^ 2 = b`. Use `hs.eq_zero` as an intermediate fact. Simplify using `at this`.

Take the linear combination `this`. Establish `hτs2 : τ s ^ 2 = b` using `by rw [← map_pow, hs2, hτb]`. Establish `hτs1 : τ s - 1 ∈ I`. Use `hI _ hs1` as an intermediate fact. Simplify using `using this`.

Establish `hsum : IsUnit (s + τ s)`. Establish `hj : (s - 1) + (τ s - 1) ∈ Ideal.jacobson (⊥ : Ideal A)` using `HenselianRing.jac (Ideal.add_mem I hs1 hτs1)`. Take `⟨v, hv⟩` from `h2.exists_right_inv`. Establish `hu` using `(Ideal.mem_jacobson_bot.1 hj) v`. Establish `: s + τ s = (((s - 1) + (τ s - 1)) * v + 1) * 2`.

Take the linear combination `(-(s - 1 + (τ s - 1))) * hv`. Rewrite using `[this]`. Conclude with `hu.mul h2`. Establish `hfix : τ s = s`. Establish `h0 : (s - τ s) * (s + τ s) = 0` using `by linear_combination hs2 - hτs2`.

Use `(hsum.mul_left_eq_zero).1 h0` as an intermediate fact. Take the linear combination `-this`. Establish `hbu : IsUnit b` using `ha.mul (IsUnit.of_mul_eq_one_right c hw)`. Establish `hsu : IsUnit s`. Rewrite `hbu` using `[← hs2, pow_two]`.

Conclude with `isUnit_of_mul_isUnit_left hbu`. Use `⟨t₀ * s, ht₀.mul hsu, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hfix]`. Establish `: t₀ * s * (τ t₀ * s) = c * s ^ 2` using `by rw [hc_def]; ring`. Rewrite using `[this, hs2, hb_def]`.

Take the linear combination `a * hw`.
-/
theorem hensel_norm_lift_of_involution :
    ∀ (A : Type) [CommRing A] (I : Ideal A) [HenselianRing A I] (τ : A →+* A), (∀ a, τ (τ a) = a) → IsUnit (2 : A) → (∀ a ∈ I, τ a ∈ I) → ∀ a t₀ : A, IsUnit a → τ a = a → IsUnit t₀ → t₀ * τ t₀ - a ∈ I → ∃ t : A, IsUnit t ∧ t * τ t = a := by
  intro A _ I _ τ hτ h2 hI a t₀ ha hτa ht₀ hclose
  set c := t₀ * τ t₀ with hc_def
  have hc : IsUnit c := ht₀.mul (ht₀.map τ)
  have hτc : τ c = c := by
    simp only [hc_def, map_mul, hτ]; ring
  obtain ⟨w, hw⟩ := hc.exists_right_inv
  have hτw : τ w = w := by
    apply hc.mul_left_cancel
    rw [hw, ← hτc, ← map_mul, hw, map_one]
  set b := a * w with hb_def
  have hτb : τ b = b := by simp only [hb_def, map_mul, hτa, hτw]
  have hb1 : 1 - b ∈ I := by
    have : 1 - b = w * (c - a) := by
      rw [hb_def]; linear_combination (-1 : A) * hw
    rw [this]; exact I.mul_mem_left w hclose
  obtain ⟨s, hs, hs1⟩ := HenselianRing.is_henselian (I := I) (X ^ 2 - C b)
    (monic_X_pow_sub_C b (by norm_num)) 1 (by simpa using hb1)
    (by
      have : (derivative (X ^ 2 - C b)).eval (1 : A) = 2 := by simp [one_add_one_eq_two]
      rw [this]; exact h2.map _)
  have hs2 : s ^ 2 = b := by
    have := hs.eq_zero; simp at this; linear_combination this
  have hτs2 : τ s ^ 2 = b := by rw [← map_pow, hs2, hτb]
  have hτs1 : τ s - 1 ∈ I := by
    have := hI _ hs1; simpa using this
  have hsum : IsUnit (s + τ s) := by
    have hj : (s - 1) + (τ s - 1) ∈ Ideal.jacobson (⊥ : Ideal A) :=
      HenselianRing.jac (Ideal.add_mem I hs1 hτs1)
    obtain ⟨v, hv⟩ := h2.exists_right_inv
    have hu := (Ideal.mem_jacobson_bot.1 hj) v
    have : s + τ s = (((s - 1) + (τ s - 1)) * v + 1) * 2 := by
      linear_combination (-(s - 1 + (τ s - 1))) * hv
    rw [this]; exact hu.mul h2
  have hfix : τ s = s := by
    have h0 : (s - τ s) * (s + τ s) = 0 := by linear_combination hs2 - hτs2
    have := (hsum.mul_left_eq_zero).1 h0
    linear_combination -this
  have hbu : IsUnit b := ha.mul (IsUnit.of_mul_eq_one_right c hw)
  have hsu : IsUnit s := by
    rw [← hs2, pow_two] at hbu; exact isUnit_of_mul_isUnit_left hbu
  refine ⟨t₀ * s, ht₀.mul hsu, ?_⟩
  rw [map_mul, hfix]
  have : t₀ * s * (τ t₀ * s) = c * s ^ 2 := by rw [hc_def]; ring
  rw [this, hs2, hb_def]
  linear_combination a * hw

end GlobalTheory
