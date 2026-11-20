import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.RamDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.NormRam
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.QuadraticNormHeckeCharRamifiedBelowRamifiedPrime

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.V.Published

namespace UpperTheory.ConvolutionTheory.Sph

/- English proof (translation)
Use `w.isPrime` as an intermediate fact. Use `haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos`. Establish `k` using `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (w.asIdeal.under (𝓞 K)) (𝓞 M) Gal(M/K)`. Rewrite `k` using `[Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(M/K), Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K), IsGalois.card_aut_eq_finrank]`. Establish `he : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1` using `fun h => hram (Ideal.ramificationIdx_eq_one_iff.1 h)`.

Establish `hd : w.asIdeal.ramificationIdx (𝓞 K) ∣ Module.finrank K M` using `⟨((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K), by rw [← k]; ring⟩`. Establish `hel` using `(Nat.dvd_prime hp).1 hd |>.resolve_left he`. Rewrite `k` using `[hel]`. Establish `h1 : ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K) = 1`. Use `Nat.eq_of_mul_eq_mul_left hp.pos ?_` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation. Conclude with `⟨Nat.eq_one_of_mul_eq_one_left h1, Nat.eq_one_of_mul_eq_one_right h1⟩`.
-/
private theorem one_of_ramified {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
    [IsGalois K M] (hp : (Module.finrank K M).Prime) (w : HeightOneSpectrum (𝓞 M))
    (hram : ¬ Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal) :
    w.asIdeal.inertiaDeg (𝓞 K) = 1 ∧ ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard = 1 := by
  have := w.isPrime
  haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos
  have k := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (w.asIdeal.under (𝓞 K)) (𝓞 M) Gal(M/K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(M/K), Ideal.inertiaDegIn_eq_inertiaDeg _ w.asIdeal Gal(M/K),
    IsGalois.card_aut_eq_finrank] at k
  have he : w.asIdeal.ramificationIdx (𝓞 K) ≠ 1 := fun h => hram (Ideal.ramificationIdx_eq_one_iff.1 h)
  have hd : w.asIdeal.ramificationIdx (𝓞 K) ∣ Module.finrank K M :=
    ⟨((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K), by rw [← k]; ring⟩
  have hel := (Nat.dvd_prime hp).1 hd |>.resolve_left he
  rw [hel] at k
  have h1 : ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
    refine Nat.eq_of_mul_eq_mul_left hp.pos ?_
    calc Module.finrank K M * (((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * w.asIdeal.inertiaDeg (𝓞 K))
        = ((w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)).ncard * (Module.finrank K M * w.asIdeal.inertiaDeg (𝓞 K)) := by ring
      _ = Module.finrank K M * 1 := by rw [k, mul_one]
  exact ⟨Nat.eq_one_of_mul_eq_one_left h1, Nat.eq_one_of_mul_eq_one_right h1⟩

end UpperTheory.ConvolutionTheory.Sph

open UpperTheory.ConvolutionTheory.Sph in
/- English proof (translation)
Introduce `K M _ _ _ _ _ _ hp w hram`. Take `⟨hf, hg⟩` from `one_of_ramified hp w hram`. Use `⟨?_, fun w' hw' => ?_, fun η hη hu => ?_⟩` and prove the remaining obligations. Establish `h` using `GlobalTheory.QuadNormChar.normV_under (K := K) w`. Rewrite `h` using `[hf, pow_one]`. Then use the resulting hypothesis.

Take `⟨a, ha⟩` from `Set.ncard_eq_one.1 hg`. Establish `h1 : w.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)` using `⟨w.isPrime, ⟨rfl⟩⟩`. Establish `h2 : w'.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M)` using `⟨w'.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hw'.symm⟩⟩`. Rewrite `h1`, `h2` using `[ha]`. Conclude with `HeightOneSpectrum.ext (h2.trans h1.symm)`.

Set `Ω` to `AlgebraicClosure M haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩`. Take `⟨A, hA⟩` from `ReciprocityTheory.Gal.exists_isPlaceOver Ω w`. Establish `hAv : IsPlaceOver A (w.under (𝓞 K))` using `fun x => by`. Rewrite using `[IsScalarTower.algebraMap_apply K M Ω]`. Conclude with `hA (algebraMap (𝓞 K) (𝓞 M) x)`.

Establish `hmove : ∃ s ∈ Ine (F` using `K) A, ¬ UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes M s := by`. Assume the negation of the conclusion as `hfix`. Use `push_neg at hfix`. Take `⟨hlo, he⟩` from `GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 K)) w hAv hA hfix`. Conclude with `hram (Ideal.ramificationIdx_eq_one_iff.1 he)`.

Conclude with `UpperTheory.Gal.UnramifiedFromSplittingCriterion.normRam K M Ω hp η hη A _ hAv hmove hu`.
-/
theorem UpperTheory.ConvolutionTheory.Sph.normRam :
    UpperTheory.ConvolutionTheory.Sph.NormRam := by
  intro K M _ _ _ _ _ _ hp w hram
  obtain ⟨hf, hg⟩ := one_of_ramified hp w hram
  refine ⟨?_, fun w' hw' => ?_, fun η hη hu => ?_⟩
  · have h := GlobalTheory.QuadNormChar.normV_under (K := K) w
    rwa [hf, pow_one] at h
  · obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 hg
    have h1 : w.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M) := ⟨w.isPrime, ⟨rfl⟩⟩
    have h2 : w'.asIdeal ∈ (w.asIdeal.under (𝓞 K)).primesOver (𝓞 M) :=
      ⟨w'.isPrime, ⟨congrArg HeightOneSpectrum.asIdeal hw'.symm⟩⟩
    rw [ha] at h1 h2
    exact HeightOneSpectrum.ext (h2.trans h1.symm)
  · let Ω := AlgebraicClosure M
    haveI : Module.Finite K M := Module.finite_of_finrank_pos hp.pos
    haveI : Algebra.IsAlgebraic M Ω := IsAlgClosure.isAlgebraic
    haveI : IsAlgClosure K Ω := ⟨IsAlgClosure.isAlgClosed M, Algebra.IsAlgebraic.trans K M Ω⟩
    obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω w
    have hAv : IsPlaceOver A (w.under (𝓞 K)) := fun x => by
      rw [IsScalarTower.algebraMap_apply K M Ω]
      exact hA (algebraMap (𝓞 K) (𝓞 M) x)
    have hmove : ∃ s ∈ Ine (F := K) A, ¬ UpperTheory.Gal.UnramifiedFromSplittingCriterion.Fixes M s := by
      by_contra hfix
      push_neg at hfix
      obtain ⟨hlo, he⟩ := GlobalTheory.InertFixVal.ramificationIdx_eq_one A (w.under (𝓞 K)) w hAv hA hfix
      exact hram (Ideal.ramificationIdx_eq_one_iff.1 he)
    exact UpperTheory.Gal.UnramifiedFromSplittingCriterion.normRam K M Ω hp η hη A _ hAv hmove hu
