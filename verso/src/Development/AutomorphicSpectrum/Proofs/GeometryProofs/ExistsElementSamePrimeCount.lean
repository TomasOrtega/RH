import Mathlib
open NumberField IsDedekindDomain UniqueFactorizationMonoid

namespace GlobalTheory.CompanionTheory.Ggeo

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Assume the hypotheses and unpack their components. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Extract witnesses or component facts from the available result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
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
