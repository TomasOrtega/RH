import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FlagBundles.Statements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FlagBundles

open MvPolynomial IsLocalRing

/- English proof (translation)
Use `set L := Localization.AtPrime (Ideal.span {a})`. Establish `: IsDomain L` using `IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))`. Establish `: IsNoetherianRing L` using `IsLocalization.isNoetherianRing (Ideal.span {a}).primeCompl L inferInstance`. Establish `hmax : maximalIdeal L = Ideal.span {algebraMap A L a}`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {a}) L, Ideal.map_span, Set.image_singleton]`.

Establish `hinj : Function.Injective (algebraMap A L)` using `IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))`. Establish `hne : algebraMap A L a ≠ 0` using `(map_ne_zero_iff _ hinj).mpr ha`. Establish `hnf : ¬ IsField L`. Rewrite using `[isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]`. Conclude with `hne`.

Establish `hdvr : IsDiscreteValuationRing L` using `((IsDiscreteValuationRing.TFAE L hnf).out 4 0).mp (⟨⟨_, hmax⟩⟩ : (maximalIdeal L).IsPrincipal)`. Conclude with `⟨hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax⟩`.
-/
theorem localization_span_singleton_dvr {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    (a : A) (ha : a ≠ 0) [hP : (Ideal.span {a}).IsPrime] :
    IsDiscreteValuationRing (Localization.AtPrime (Ideal.span {a})) ∧
      Irreducible (algebraMap A (Localization.AtPrime (Ideal.span {a})) a) := by
  set L := Localization.AtPrime (Ideal.span {a})
  have : IsDomain L :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))
  have : IsNoetherianRing L :=
    IsLocalization.isNoetherianRing (Ideal.span {a}).primeCompl L inferInstance
  have hmax : maximalIdeal L = Ideal.span {algebraMap A L a} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (Ideal.span {a}) L, Ideal.map_span,
      Set.image_singleton]
  have hinj : Function.Injective (algebraMap A L) :=
    IsLocalization.injective L (Ideal.primeCompl_le_nonZeroDivisors (Ideal.span {a}))
  have hne : algebraMap A L a ≠ 0 := (map_ne_zero_iff _ hinj).mpr ha
  have hnf : ¬ IsField L := by
    rw [isField_iff_maximalIdeal_eq, hmax, Ideal.span_singleton_eq_bot]
    exact hne
  have hdvr : IsDiscreteValuationRing L :=
    ((IsDiscreteValuationRing.TFAE L hnf).out 4 0).mp (⟨⟨_, hmax⟩⟩ : (maximalIdeal L).IsPrincipal)
  exact ⟨hdvr, (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr hmax⟩

/- English proof (translation)
Introduce `R _ _ _`. Establish `hd : (diagonalIdeal R).IsPrime`. Rewrite using `[← Ideal.Quotient.isDomain_iff_prime]`. Conclude with `(h0 R).2.2.1 inferInstance`. Establish `hm : (mixedDiagonalIdeal R).IsPrime`.

Rewrite using `[← Ideal.Quotient.isDomain_iff_prime]`. Conclude with `(h0 R).2.2.2.2.2 inferInstance`. Establish `h1 : (X 0 - X 1 : MvPolynomial (Fin 2) R) ≠ 0`. Introduce `h`. Use `congrArg (MvPolynomial.eval ![(1 : R), 0]) h` as an intermediate fact.

Simplify using `at this`. Establish `h2 : (1 - X 0 * X 1 : MvPolynomial (Fin 2) R) ≠ 0`. Introduce `h`. Use `congrArg (MvPolynomial.eval ![(0 : R), 0]) h` as an intermediate fact. Simplify using `at this`.

Conclude with `⟨⟨hd, @localization_span_singleton_dvr _ _ _ _ _ h1 hd⟩, ⟨hm, @localization_span_singleton_dvr _ _ _ _ _ h2 hm⟩⟩`.
-/
theorem DiagonalLocalDVR.proof (h0 : DiagonalQuotient.Statement) : DiagonalLocalDVR.Statement := by
  intro R _ _ _
  have hd : (diagonalIdeal R).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (h0 R).2.2.1 inferInstance
  have hm : (mixedDiagonalIdeal R).IsPrime := by
    rw [← Ideal.Quotient.isDomain_iff_prime]
    exact (h0 R).2.2.2.2.2 inferInstance
  have h1 : (X 0 - X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![(1 : R), 0]) h
    simp at this
  have h2 : (1 - X 0 * X 1 : MvPolynomial (Fin 2) R) ≠ 0 := by
    intro h
    have := congrArg (MvPolynomial.eval ![(0 : R), 0]) h
    simp at this
  exact ⟨⟨hd, @localization_span_singleton_dvr _ _ _ _ _ h1 hd⟩,
    ⟨hm, @localization_span_singleton_dvr _ _ _ _ _ h2 hm⟩⟩

end GroundTheory.Heights₂.Heights.FlagBundles
