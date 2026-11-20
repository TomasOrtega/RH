import Mathlib
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Ggeo

/- English proof (translation)
Introduce `R _ _ I P hI hP hP0`. Establish `hlt : I * P < I`. Use `lt_of_le_of_ne Ideal.mul_le_left fun h => hP.ne_top ?_` and prove the remaining obligations. Establish `h' : I * P = I * ⊤` using `by rw [h, Ideal.mul_top]`. Conclude with `mul_left_cancel₀ hI h'`.

Take `⟨x, hxI, hxIP⟩` from `SetLike.exists_of_lt hlt`. Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `hxIP (Submodule.zero_mem _)`. Use `⟨x, hxI, hx0, ?_⟩` and prove the remaining obligations.

Take `⟨J, hJ⟩ : I ∣ Ideal.span {x}` from `Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxI)`. Establish `hJ0 : J ≠ ⊥`. Introduce and unpack `rfl`. Rewrite `hJ` using `[Ideal.mul_bot, Ideal.span_singleton_eq_bot]`. Conclude with `hx0 hJ`.

Establish `hPJ : (normalizedFactors J).count P = 0`. Rewrite using `[Multiset.count_eq_zero]`. Introduce `hmem`. Take `⟨K, rfl⟩` from `dvd_of_mem_normalizedFactors hmem`. Apply `hxIP` to reduce the goal to its premises.

Establish `hle : Ideal.span {x} ≤ I * P`. Rewrite using `[hJ, ← mul_assoc]`. Conclude with `Ideal.mul_le_left`. Conclude with `hle (Ideal.mem_span_singleton_self x)`. Rewrite using `[hJ, normalizedFactors_mul hI hJ0, Multiset.count_add, hPJ, add_zero]`.
-/
theorem exists_mem_count_normalizedFactors_span_eq :
    ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (I P : Ideal R), I ≠ ⊥ → P.IsPrime → P ≠ ⊥ →
      ∃ x ∈ I, x ≠ 0 ∧
        (normalizedFactors (Ideal.span {x})).count P = (normalizedFactors I).count P := by
  intro R _ _ I P hI hP hP0
  have hlt : I * P < I := by
    refine lt_of_le_of_ne Ideal.mul_le_left fun h => hP.ne_top ?_
    have h' : I * P = I * ⊤ := by rw [h, Ideal.mul_top]
    exact mul_left_cancel₀ hI h'
  obtain ⟨x, hxI, hxIP⟩ := SetLike.exists_of_lt hlt
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxIP (Submodule.zero_mem _)
  refine ⟨x, hxI, hx0, ?_⟩
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {x} :=
    Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hxI)
  have hJ0 : J ≠ ⊥ := by
    rintro rfl
    rw [Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact hx0 hJ
  have hPJ : (normalizedFactors J).count P = 0 := by
    rw [Multiset.count_eq_zero]
    intro hmem
    obtain ⟨K, rfl⟩ := dvd_of_mem_normalizedFactors hmem
    apply hxIP
    have hle : Ideal.span {x} ≤ I * P := by
      rw [hJ, ← mul_assoc]
      exact Ideal.mul_le_left
    exact hle (Ideal.mem_span_singleton_self x)
  rw [hJ, normalizedFactors_mul hI hJ0, Multiset.count_add, hPJ, add_zero]

end GlobalTheory.CompanionTheory.Ggeo
