import Mathlib
open NumberField IsDedekindDomain Polynomial

namespace GlobalTheory

/- English proof (translation)
Introduce `K _ _ x a b hx hab`. Use `⟨fun v => ?_⟩` and prove the remaining obligations. Rewrite using `[← NumberField.InfinitePlace.not_isReal_iff_isComplex]`. Introduce `hv`. Use `set φ : K →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hv`.

Establish `h` using `congrArg φ hx`. Simplify using `only [map_add, map_mul, map_pow, map_intCast, map_zero] at h`. Establish `hab' : ((a : ℝ)) ^ 2 < 4 * (b : ℝ)` using `by exact_mod_cast hab`. Use polynomial arithmetic with `[sq_nonneg (2 * φ x + (a : ℝ))]`.
-/
theorem totallyComplex_of_root_quadratic_neg_disc :
    ∀ (K : Type) [Field K] [NumberField K] (x : K) (a b : ℤ), x ^ 2 + (a : K) * x + (b : K) = 0 →
    a ^ 2 < 4 * b → NumberField.IsTotallyComplex K := by
  intro K _ _ x a b hx hab
  refine ⟨fun v => ?_⟩
  rw [← NumberField.InfinitePlace.not_isReal_iff_isComplex]
  intro hv
  set φ : K →+* ℝ := NumberField.InfinitePlace.embedding_of_isReal hv
  have h := congrArg φ hx
  simp only [map_add, map_mul, map_pow, map_intCast, map_zero] at h
  have hab' : ((a : ℝ)) ^ 2 < 4 * (b : ℝ) := by exact_mod_cast hab
  nlinarith [sq_nonneg (2 * φ x + (a : ℝ))]

end GlobalTheory
