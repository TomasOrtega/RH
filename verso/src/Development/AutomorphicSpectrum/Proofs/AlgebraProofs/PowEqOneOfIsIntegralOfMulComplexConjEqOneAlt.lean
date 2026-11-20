import Mathlib

open MeasureTheory NumberField Matrix Filter Topology
open scoped Pointwise ENNReal

namespace GlobalTheory.CompanionTheory.Ar.Cmp

/- English proof (translation)
Establish `hn : ∀ φ : E →+* ℂ, ‖φ z‖ = 1`. Introduce `φ`. Establish `h1` using `congrArg φ h`. Rewrite `h1` using `[map_mul, map_one, IsCMField.complexEmbedding_complexConj]`. Establish `h2` using `congrArg norm h1`.

Rewrite `h2` using `[norm_mul, norm_one, RCLike.norm_conj]`. Establish `h0` using `norm_nonneg (φ z)`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨n, hn0, hn1⟩` from `NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hz hn`. Conclude with `⟨n, hn0, hn1⟩`.
-/
theorem pow_eq_one_of_isIntegral_of_mul_complexConj_eq_one
    (E : Type) [Field E] [NumberField E] [IsCMField E] (z : E) (hz : IsIntegral ℤ z)
    (h : z * IsCMField.complexConj E z = 1) : ∃ n : ℕ, 0 < n ∧ z ^ n = 1 := by
  have hn : ∀ φ : E →+* ℂ, ‖φ z‖ = 1 := by
    intro φ
    have h1 := congrArg φ h
    rw [map_mul, map_one, IsCMField.complexEmbedding_complexConj] at h1
    have h2 := congrArg norm h1
    rw [norm_mul, norm_one, RCLike.norm_conj] at h2
    have h0 := norm_nonneg (φ z)
    nlinarith
  obtain ⟨n, hn0, hn1⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hz hn
  exact ⟨n, hn0, hn1⟩

end GlobalTheory.CompanionTheory.Ar.Cmp
