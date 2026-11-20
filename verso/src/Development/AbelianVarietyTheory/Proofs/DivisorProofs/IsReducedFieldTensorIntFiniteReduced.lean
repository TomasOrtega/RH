import Mathlib
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FinRedTensor

/- English proof (translation)
Take `⟨p, hp⟩` from `CharP.exists K`. Use `haveI : NeZero p := ⟨CharP.char_ne_zero_of_finite K p⟩`. Use `haveI : Fact p.Prime := CharP.char_is_prime_of_pos K p`. Use `letI : Algebra (ZMod p) K := ZMod.algebra K p`. Use `haveI : Module.Finite (ZMod p) K := Module.Finite.of_finite`.

Use `haveI : Algebra.IsSeparable (ZMod p) K := inferInstance`. Use `haveI : Algebra.FormallyUnramified (ZMod p) K := Algebra.FormallyUnramified.of_isSeparable _ _`. Use `haveI : Algebra.FormallyUnramified ℤ (ZMod p) := Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (ZMod p)) (ZMod.intCast_surjective)`. Conclude with `Algebra.FormallyUnramified.comp ℤ (ZMod p) K`.
-/
theorem formallyUnramified_int_of_finite_field (K : Type) [Field K] [Finite K] :
    Algebra.FormallyUnramified ℤ K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : NeZero p := ⟨CharP.char_ne_zero_of_finite K p⟩
  haveI : Fact p.Prime := CharP.char_is_prime_of_pos K p
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Module.Finite (ZMod p) K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (ZMod p) K := inferInstance
  haveI : Algebra.FormallyUnramified (ZMod p) K := Algebra.FormallyUnramified.of_isSeparable _ _
  haveI : Algebra.FormallyUnramified ℤ (ZMod p) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (ZMod p)) (ZMod.intCast_surjective)
  exact Algebra.FormallyUnramified.comp ℤ (ZMod p) K

/- English proof (translation)
Use `haveI : IsArtinianRing A := inferInstance`. Establish `h : Algebra.FormallyUnramified ℤ (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal)`. Rewrite using `[Algebra.FormallyUnramified.pi_iff]`. Introduce `I`. Use `I.isMaximal` as an intermediate fact.

Use `letI := Ideal.Quotient.field I.asIdeal`. Use `haveI : Finite (A ⧸ I.asIdeal) := Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective`. Conclude with `formallyUnramified_int_of_finite_field _`. Conclude with `Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars ℤ).symm`.
-/
theorem formallyUnramified_int_of_finite_isReduced (A : Type) [CommRing A] [Finite A]
    [IsReduced A] : Algebra.FormallyUnramified ℤ A := by
  haveI : IsArtinianRing A := inferInstance
  have h : Algebra.FormallyUnramified ℤ (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    haveI : Finite (A ⧸ I.asIdeal) :=
      Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
    exact formallyUnramified_int_of_finite_field _
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars ℤ).symm

/- English proof (translation)
Introduce `A _ _ _ k _`. Use `haveI := formallyUnramified_int_of_finite_isReduced A`. Use `haveI : Algebra.FormallyUnramified k (k ⊗[ℤ] A) := Algebra.FormallyUnramified.base_change k`. Use `haveI : Module.Finite ℤ A := Module.Finite.of_finite`. Use `haveI : Algebra.EssFiniteType k (k ⊗[ℤ] A) := inferInstance`.

Conclude with `Algebra.FormallyUnramified.isReduced_of_field k _`.
-/
theorem isReduced_field_tensor_finite :
    ∀ (A : Type) [CommRing A] [Finite A] [IsReduced A] (k : Type) [Field k],
      IsReduced (k ⊗[ℤ] A) := by
  intro A _ _ _ k _
  haveI := formallyUnramified_int_of_finite_isReduced A
  haveI : Algebra.FormallyUnramified k (k ⊗[ℤ] A) := Algebra.FormallyUnramified.base_change k
  haveI : Module.Finite ℤ A := Module.Finite.of_finite
  haveI : Algebra.EssFiniteType k (k ⊗[ℤ] A) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field k _

end GlobalTheory.FinRedTensor
