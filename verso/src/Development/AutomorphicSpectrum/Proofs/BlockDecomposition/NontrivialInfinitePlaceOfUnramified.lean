import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt

open NumberField IsDedekindDomain

namespace GlobalTheory.CompanionTheory.UnrCM

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Simplify to obtain the desired conclusion from the available facts.
-/
theorem algebraMap_int_ringOfIntegers_surjective (F : Type) [Field F] [NumberField F]
    (h : Module.finrank ℚ F = 1) : Function.Surjective (algebraMap ℤ (𝓞 F)) := by
  intro x
  obtain ⟨q, hq⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h).2 (x : F)
  have hint : IsIntegral ℤ q :=
    (isIntegral_algebraMap_iff (algebraMap ℚ F).injective).1 (hq ▸ x.isIntegral_coe)
  obtain ⟨n, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
  refine ⟨n, RingOfIntegers.ext ?_⟩
  simpa using hq

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Use linear arithmetic over natural numbers and integers.
-/
theorem finrank_maximalRealSubfield_of_subsingleton (E : Type) [Field E] [NumberField E] [IsCMField E]
    [Subsingleton (InfinitePlace E)] : Module.finrank ℚ (maximalRealSubfield E) = 1 := by
  have h1 : Fintype.card (InfinitePlace E) = 1 :=
    le_antisymm (Fintype.card_le_one_iff_subsingleton.2 inferInstance) Fintype.card_pos
  have h2 : Module.finrank ℚ E = 2 * InfinitePlace.nrComplexPlaces E := IsTotallyComplex.finrank E
  have h3 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := E)
  have h4 : InfinitePlace.nrRealPlaces E = 0 := IsTotallyComplex.nrRealPlaces_eq_zero E
  have h5 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
  rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E] at h5
  omega

/- English proof (translation)
Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Use linear arithmetic over natural numbers and integers. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

A detailed English derivation is pending.
-/
theorem nontrivial_infinitePlace_of_forall_isUnramifiedAt (E : Type) [Field E] [NumberField E] [IsCMField E]
    (hU : ∀ w : HeightOneSpectrum (𝓞 E), Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield E)) w.asIdeal) :
    Nontrivial (InfinitePlace E) := by
  by_contra hn
  haveI : Subsingleton (InfinitePlace E) := not_nontrivial_iff_subsingleton.1 hn
  have hF := finrank_maximalRealSubfield_of_subsingleton E
  have hE : Module.finrank ℚ E ≠ 1 := by
    have h5 := Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E
    rw [Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, hF] at h5
    omega
  obtain ⟨P, hP, hram⟩ := NumberField.exists_not_isUnramifiedAt_int (K := E) (𝒪 := 𝓞 E) hE
  have hbot : P ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)
  have hw := hU ⟨P, hP.isPrime, hbot⟩
  apply hram
  haveI : Algebra.FormallyUnramified (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P) := hw
  haveI : Algebra.FormallyUnramified ℤ (𝓞 (maximalRealSubfield E)) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ _)
      (algebraMap_int_ringOfIntegers_surjective _ hF)
  exact Algebra.FormallyUnramified.comp ℤ (𝓞 (maximalRealSubfield E)) (Localization.AtPrime P)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem nontrivial_infinitePlace :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.BCT.Unr E → Nontrivial (InfinitePlace E) :=
  fun E _ _ _ hU => nontrivial_infinitePlace_of_forall_isUnramifiedAt E hU

end GlobalTheory.CompanionTheory.UnrCM
