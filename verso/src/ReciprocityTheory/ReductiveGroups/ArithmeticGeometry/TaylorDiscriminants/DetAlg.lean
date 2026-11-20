import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.TB

def DetAlgSt : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K)), I.IsRadical →
    ∀ r : MvPolynomial (Fin n) K ⧸ I,
      (∀ (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
        (φ : (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] L), φ r = 0) → r = 0

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Equip the data with the indicated structure. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem detAlg_holds : DetAlgSt := by
  intro K _ n I hI r hr
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [Ideal.Quotient.eq_zero_iff_mem, ← IsJacobsonRing.out inferInstance hI]
  unfold Ideal.jacobson
  rw [Ideal.mem_sInf]
  rintro J ⟨hIJ, hJ⟩
  haveI := hJ
  letI : Field (MvPolynomial (Fin n) K ⧸ J) := Ideal.Quotient.field J
  haveI : Algebra.FiniteType K (MvPolynomial (Fin n) K ⧸ J) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J)
      (Ideal.Quotient.mkₐ_surjective K J)
  haveI : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ J) :=
    finite_of_finite_type_of_isJacobsonRing K _
  have h := hr (MvPolynomial (Fin n) K ⧸ J) (Ideal.Quotient.factorₐ K hIJ)
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact h

/- English proof (translation)
A detailed English derivation is pending.
-/
example : (⊥ : Ideal (MvPolynomial (Fin 0) ℚ)).IsRadical := Ideal.isRadical_bot

end ReciprocityTheory.ChartRestriction.G.TB
