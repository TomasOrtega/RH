import Mathlib

namespace ReciprocityTheory.ChartRestriction.G.TB

def DetAlgSt : Prop :=
  ∀ (K : Type) [Field K] (n : ℕ) (I : Ideal (MvPolynomial (Fin n) K)), I.IsRadical →
    ∀ r : MvPolynomial (Fin n) K ⧸ I,
      (∀ (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L]
        (φ : (MvPolynomial (Fin n) K ⧸ I) →ₐ[K] L), φ r = 0) → r = 0

/- English proof (translation)
Introduce `K _ n I hI r hr`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective r`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem, ← IsJacobsonRing.out inferInstance hI]`. Unfold `Ideal.jacobson`. Rewrite using `[Ideal.mem_sInf]`.

Introduce and unpack `J ⟨hIJ, hJ⟩`. Use `haveI := hJ`. Use `letI : Field (MvPolynomial (Fin n) K ⧸ J) := Ideal.Quotient.field J`. Use `haveI : Algebra.FiniteType K (MvPolynomial (Fin n) K ⧸ J) := Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) (Ideal.Quotient.mkₐ_surjective K J)`. Use `haveI : FiniteDimensional K (MvPolynomial (Fin n) K ⧸ J) := finite_of_finite_type_of_isJacobsonRing K _`.

Establish `h` using `hr (MvPolynomial (Fin n) K ⧸ J) (Ideal.Quotient.factorₐ K hIJ)`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h`.
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
The claim follows from `Ideal.isRadical_bot`.
-/
example : (⊥ : Ideal (MvPolynomial (Fin 0) ℚ)).IsRadical := Ideal.isRadical_bot

end ReciprocityTheory.ChartRestriction.G.TB
