import Mathlib

namespace GlobalTheory

/- English proof (translation)
Establish `hM : (1 : ℝ) ≤ max 1 t⁻¹` using `le_max_left _ _`. Establish `hM0 : (0 : ℝ) ≤ max 1 t⁻¹` using `le_trans zero_le_one hM`. Use `⟨(max 1 t⁻¹) ^ a, pow_nonneg hM0 _, fun r hr hstep p q hpq => ?_⟩` and prove the remaining obligations. Establish `key : ∀ (n : ℕ) (h : (p : ℕ) + n < a), r ⟨p + n, h⟩ ≤ (max 1 t⁻¹) ^ n * r p`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro h`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `h`.

Establish `h' : (p : ℕ) + n < a` using `by omega`. Establish `h1` using `hstep ⟨p + n, h'⟩ ⟨p + (n + 1), h⟩ (by simp [add_assoc])`. Establish `h2 : r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩`. Rewrite using `[inv_mul_eq_div, le_div_iff₀ ht, mul_comm]`. Conclude with `h1`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpq' : (p : ℕ) ≤ q` using `hpq`. Establish `hlt : (p : ℕ) + (q - p) < a` using `by have := q.2; omega`. Establish `hq : (⟨p + (q - p), hlt⟩ : Fin a) = q` using `Fin.ext (by simp only; omega)`. Establish `h3` using `key (q - p) hlt`.

Rewrite `h3` using `[hq]`. Rewrite using `[div_le_iff₀ (hr p)]`. Use `h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM ?_) (hr p).le)` and prove the remaining obligations. Use `q.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem cone_ratio_bounded (a : ℕ) (t : ℝ) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : Fin a → ℝ, (∀ i, 0 < r i) →
      (∀ i j : Fin a, (j : ℕ) = i + 1 → t * r j ≤ r i) →
      ∀ p q : Fin a, p ≤ q → r q / r p ≤ C := by
  have hM : (1 : ℝ) ≤ max 1 t⁻¹ := le_max_left _ _
  have hM0 : (0 : ℝ) ≤ max 1 t⁻¹ := le_trans zero_le_one hM
  refine ⟨(max 1 t⁻¹) ^ a, pow_nonneg hM0 _, fun r hr hstep p q hpq => ?_⟩
  have key : ∀ (n : ℕ) (h : (p : ℕ) + n < a), r ⟨p + n, h⟩ ≤ (max 1 t⁻¹) ^ n * r p := by
    intro n
    induction n with
    | zero => intro h; simp
    | succ n ih =>
      intro h
      have h' : (p : ℕ) + n < a := by omega
      have h1 := hstep ⟨p + n, h'⟩ ⟨p + (n + 1), h⟩ (by simp [add_assoc])
      have h2 : r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩ := by
        rw [inv_mul_eq_div, le_div_iff₀ ht, mul_comm]; exact h1
      calc r ⟨p + (n + 1), h⟩ ≤ t⁻¹ * r ⟨p + n, h'⟩ := h2
        _ ≤ max 1 t⁻¹ * r ⟨p + n, h'⟩ :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) (hr _).le
        _ ≤ max 1 t⁻¹ * ((max 1 t⁻¹) ^ n * r p) := mul_le_mul_of_nonneg_left (ih h') hM0
        _ = (max 1 t⁻¹) ^ (n + 1) * r p := by ring
  have hpq' : (p : ℕ) ≤ q := hpq
  have hlt : (p : ℕ) + (q - p) < a := by have := q.2; omega
  have hq : (⟨p + (q - p), hlt⟩ : Fin a) = q := Fin.ext (by simp only; omega)
  have h3 := key (q - p) hlt
  rw [hq] at h3
  rw [div_le_iff₀ (hr p)]
  refine h3.trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hM ?_) (hr p).le)
  have := q.2; omega

end GlobalTheory
