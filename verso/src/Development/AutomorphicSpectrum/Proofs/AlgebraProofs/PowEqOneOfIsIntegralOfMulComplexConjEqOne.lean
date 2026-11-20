import Mathlib
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

/- English proof (translation)
Introduce `E _ _ _ u hu h`. Establish `hn : ∀ s : E →+* ℂ, ‖s u‖ = 1`. Introduce `s`. Establish `h1 : s u * (starRingEnd ℂ) (s u) = 1`. Rewrite using `[← IsCMField.complexEmbedding_complexConj, ← map_mul, h, map_one]`.

Establish `h2 : ‖s u‖ ^ 2 = 1`. Use `congrArg norm h1` as an intermediate fact. Rewrite `this` using `[norm_mul, Complex.norm_conj, norm_one]`. Rewrite using `[sq, this]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2`.

Take `⟨n, hn0, hn1⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hu hn`. Conclude with `⟨n, hn0, hn1⟩`.
-/
theorem pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (u : E), IsIntegral ℤ u →
      u * IsCMField.complexConj E u = 1 → ∃ n : ℕ, 0 < n ∧ u ^ n = 1 := by
  intro E _ _ _ u hu h
  have hn : ∀ s : E →+* ℂ, ‖s u‖ = 1 := by
    intro s
    have h1 : s u * (starRingEnd ℂ) (s u) = 1 := by
      rw [← IsCMField.complexEmbedding_complexConj, ← map_mul, h, map_one]
    have h2 : ‖s u‖ ^ 2 = 1 := by
      have := congrArg norm h1
      rw [norm_mul, Complex.norm_conj, norm_one] at this
      rw [sq, this]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  obtain ⟨n, hn0, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hu hn
  exact ⟨n, hn0, hn1⟩

end GlobalTheory.CompanionTheory.Ar.Flat
