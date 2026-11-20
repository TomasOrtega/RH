import Mathlib

namespace GlobalTheory

open Module in

/- English proof (translation)
Introduce `R M _ _ _ _ _ r hr s hs`. Establish `hspan : Submodule.span R (Set.range s) = ⊤`. Establish `: Subsingleton (M ⧸ Submodule.span R (Set.range s))` using `Module.support_eq_empty_iff.1 hs`. Conclude with `Submodule.Quotient.subsingleton_iff.1 this`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[← linearIndependent_iff_injective_fintypeLinearCombination]`. Use `LinearIndependent.of_isLocalized_maximal (fun P _ => Localization.AtPrime P) (fun P _ => LocalizedModule P.primeCompl M) (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M) s fun P hP => ?_` and prove the remaining obligations. Establish `hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M)` using `Module.free_of_flat_of_isLocalRing`. Establish `hrk : Module.finrank (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = r` using `hr ⟨P, hP.isPrime⟩`. Establish `hsp : Submodule.span (Localization.AtPrime P) (Set.range (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) = ⊤`.

Rewrite using `[Set.range_comp]`. Conclude with `span_eq_top_of_isLocalizedModule (Localization.AtPrime P) P.primeCompl (LocalizedModule.mkLinearMap P.primeCompl M) hspan`. Establish `hsurj : Function.Surjective (Fintype.linearCombination (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M ∘ s))`. Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp]`. Set `b` to `Module.finBasisOfFinrankEq (Localization.AtPrime P) (LocalizedModule P.primeCompl M) hrk`.

Establish `hinj` using `OrzechProperty.injective_of_surjective_endomorphism (b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination (Localization.AtPrime P) (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) (b.equivFun.surjective.comp hsurj)`. Rewrite using `[linearIndependent_iff_injective_fintypeLinearCombination]`. Conclude with `Function.Injective.of_comp (f := ⇑b.equivFun) hinj`. Rewrite using `[← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]`.
-/
theorem bijective_linearCombination_of_rankAtStalk :
    ∀ (R M : Type) [CommRing R] [AddCommGroup M] [Module R M] [Module.Finite R M] [Module.Flat R M] (r : ℕ),
      (∀ p : PrimeSpectrum R, Module.rankAtStalk M p = r) → ∀ s : Fin r → M,
      Module.support R (M ⧸ Submodule.span R (Set.range s)) = ∅ →
      Function.Bijective (Fintype.linearCombination R s) := by
  intro R M _ _ _ _ _ r hr s hs
  have hspan : Submodule.span R (Set.range s) = ⊤ := by
    have : Subsingleton (M ⧸ Submodule.span R (Set.range s)) := Module.support_eq_empty_iff.1 hs
    exact Submodule.Quotient.subsingleton_iff.1 this
  refine ⟨?_, ?_⟩
  · rw [← linearIndependent_iff_injective_fintypeLinearCombination]
    refine LinearIndependent.of_isLocalized_maximal (fun P _ => Localization.AtPrime P)
      (fun P _ => LocalizedModule P.primeCompl M) (fun P _ => LocalizedModule.mkLinearMap P.primeCompl M)
      s fun P hP => ?_
    have hfree : Module.Free (Localization.AtPrime P) (LocalizedModule P.primeCompl M) :=
      Module.free_of_flat_of_isLocalRing
    have hrk : Module.finrank (Localization.AtPrime P) (LocalizedModule P.primeCompl M) = r :=
      hr ⟨P, hP.isPrime⟩
    have hsp : Submodule.span (Localization.AtPrime P)
        (Set.range (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) = ⊤ := by
      rw [Set.range_comp]
      exact span_eq_top_of_isLocalizedModule (Localization.AtPrime P) P.primeCompl
        (LocalizedModule.mkLinearMap P.primeCompl M) hspan
    have hsurj : Function.Surjective (Fintype.linearCombination (Localization.AtPrime P)
        (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) := by
      rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hsp]
    let b := Module.finBasisOfFinrankEq (Localization.AtPrime P) (LocalizedModule P.primeCompl M) hrk
    have hinj := OrzechProperty.injective_of_surjective_endomorphism
      (b.equivFun.toLinearMap ∘ₗ Fintype.linearCombination (Localization.AtPrime P)
        (LocalizedModule.mkLinearMap P.primeCompl M ∘ s)) (b.equivFun.surjective.comp hsurj)
    rw [linearIndependent_iff_injective_fintypeLinearCombination]
    exact Function.Injective.of_comp (f := ⇑b.equivFun) hinj
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination, hspan]

end GlobalTheory
