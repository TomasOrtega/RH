import Mathlib
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Use `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_` and prove the remaining obligations. Use `Monotone.strictMono_of_injective ?_ (PrimeSpectrum.localization_comap_injective S M)` and prove the remaining obligations. Introduce `p q h`. Conclude with `Ideal.comap_mono h`.
-/
theorem ringKrullDim_le_of_isLocalization' {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (M : Submonoid R) [IsLocalization M S] : ringKrullDim S ≤ ringKrullDim R := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S)) ?_
  refine Monotone.strictMono_of_injective ?_ (PrimeSpectrum.localization_comap_injective S M)
  intro p q h
  exact Ideal.comap_mono h

open IsLocalRing in
/- English proof (translation)
Use `Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A D)) ?_` and prove the remaining obligations. Use `Monotone.strictMono_of_injective (fun p q h => ?_) (PrimeSpectrum.localization_comap_injective D M)` and prove the remaining obligations. Conclude with `Ideal.comap_mono h`.
-/
private theorem ringKrullDim_le_of_isLocalization (A D : Type) [CommRing A] [CommRing D]
    [Algebra A D] (M : Submonoid A) [IsLocalization M D] :
    ringKrullDim D ≤ ringKrullDim A := by
  refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A D)) ?_
  refine Monotone.strictMono_of_injective (fun p q h => ?_)
    (PrimeSpectrum.localization_comap_injective D M)
  exact Ideal.comap_mono h

open IsLocalRing in
/- English proof (translation)
Take `⟨n, f, hf⟩` from `Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›`. Use `lt_of_le_of_lt (ringKrullDim_le_of_surjective f.toRingHom hf) ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.ringKrullDim_of_isNoetherianRing, IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]`. Establish `h : ((1 + Nat.card (Fin n) : ℕ) : WithBot ℕ∞) < ⊤` using `WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)`. Conclude with `h` after adjusting the coercions.
-/
private theorem ringKrullDim_finite_of_finiteType_int (A : Type) [CommRing A]
    [Algebra.FiniteType ℤ A] : ringKrullDim A < ⊤ := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp ‹_›
  refine lt_of_le_of_lt (ringKrullDim_le_of_surjective f.toRingHom hf) ?_
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing,
    IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField]
  have h : ((1 + Nat.card (Fin n) : ℕ) : WithBot ℕ∞) < ⊤ :=
    WithBot.coe_lt_coe.mpr (ENat.coe_lt_top _)
  exact_mod_cast h

open IsLocalRing in

/- English proof (translation)
The claim follows from `lt_of_le_of_lt (ringKrullDim_le_of_isLocalization (Algebra.EssFiniteType.subalgebra ℤ D) D (Algebra.EssFiniteType.submonoid ℤ D)) (ringKrullDim_finite_of_finiteType_int _)`.
-/
theorem _root_.GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D] :
    ringKrullDim D < ⊤ :=
  lt_of_le_of_lt
    (ringKrullDim_le_of_isLocalization (Algebra.EssFiniteType.subalgebra ℤ D) D
      (Algebra.EssFiniteType.submonoid ℤ D))
    (ringKrullDim_finite_of_finiteType_int _)

end GlobalTheory
