import Mathlib

open NumberField

namespace GlobalTheory

/- English proof (translation)
Assume the negation of the conclusion as `ht`. Take `⟨s, rfl⟩` from `hd`. Establish `hs : s ≠ 0`. Introduce and unpack `rfl`. Conclude with `ht (mul_zero _)`.

Take `⟨σ, hσ⟩` from `NumberField.exists_conjugate_one_le_norm hs`. Establish `h1` using `hB σ`. Establish `hcast : (((g₀ : 𝓞 E) * s : 𝓞 E) : E) = (g₀ : E) * (s : E)`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite `h1` using `[hcast, map_mul, map_natCast, norm_mul, Complex.norm_natCast]`. Establish `h2 : (g₀ : ℝ) ≤ g₀ * ‖σ (s : E)‖` using `le_mul_of_one_le_right (Nat.cast_nonneg _) hσ`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem ringOfIntegers_eq_zero_of_natCast_dvd_of_norm_embedding_le
    (E : Type) [Field E] [NumberField E] (g₀ : ℕ) (B : ℝ) (t : 𝓞 E)
    (hd : (g₀ : 𝓞 E) ∣ t) (hB : ∀ ι : E →+* ℂ, ‖ι (t : E)‖ ≤ B) (hlt : B < g₀) : t = 0 := by
  by_contra ht
  obtain ⟨s, rfl⟩ := hd
  have hs : s ≠ 0 := by
    rintro rfl
    exact ht (mul_zero _)
  obtain ⟨σ, hσ⟩ := NumberField.exists_conjugate_one_le_norm hs
  have h1 := hB σ
  have hcast : (((g₀ : 𝓞 E) * s : 𝓞 E) : E) = (g₀ : E) * (s : E) := by
    push_cast
    rfl
  rw [hcast, map_mul, map_natCast, norm_mul, Complex.norm_natCast] at h1
  have h2 : (g₀ : ℝ) ≤ g₀ * ‖σ (s : E)‖ := le_mul_of_one_le_right (Nat.cast_nonneg _) hσ
  linarith

end GlobalTheory
