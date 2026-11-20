import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

/- English proof (translation)
Introduce `O k _ _ _ _ _ Y p`. Use `haveI : IsPreimmersion (gen O k) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)`. Establish `hker : RingHom.ker (algebraMap O k) = ⊥` using `(RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O k)`. Use `⟨?_, (pullback.fst p (gen O k)).isEmbedding⟩` and prove the remaining obligations. Rewrite using `[Scheme.Pullback.range_fst]`.

Use extensionality with `y`. Simplify using `only [Set.mem_preimage, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Rewrite using `[← hz]`.

Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap O k) (z : PrimeSpectrum k).asIdeal = ⊥`. Use `haveI : (z : PrimeSpectrum k).asIdeal.IsPrime := (z : PrimeSpectrum k).isPrime`. Rewrite using `[Ideal.eq_bot_of_prime (z : PrimeSpectrum k).asIdeal, ← RingHom.ker_eq_comap_bot, hker]`. Introduce `h`. Use `⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩` and prove the remaining obligations.

Apply `PrimeSpectrum.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Ideal.comap (algebraMap O k) ⊥ = (p y).asIdeal`. Rewrite using `[h, ← RingHom.ker_eq_comap_bot, hker]`.
-/
theorem UpperTheory.Gal.Int.Geo.Cut.genRange :
    UpperTheory.Gal.Int.Geo.Cut.GenRange := by
  intro O k _ _ _ _ _ Y p
  haveI : IsPreimmersion (gen O k) := IsPreimmersion.of_isLocalization (nonZeroDivisors O)
  have hker : RingHom.ker (algebraMap O k) = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp (IsFractionRing.injective O k)
  refine ⟨?_, (pullback.fst p (gen O k)).isEmbedding⟩
  rw [Scheme.Pullback.range_fst]
  ext y
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, hz⟩
    rw [← hz]
    change Ideal.comap (algebraMap O k) (z : PrimeSpectrum k).asIdeal = ⊥
    haveI : (z : PrimeSpectrum k).asIdeal.IsPrime := (z : PrimeSpectrum k).isPrime
    rw [Ideal.eq_bot_of_prime (z : PrimeSpectrum k).asIdeal, ← RingHom.ker_eq_comap_bot, hker]
  · intro h
    refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum k), ?_⟩
    apply PrimeSpectrum.ext
    change Ideal.comap (algebraMap O k) ⊥ = (p y).asIdeal
    rw [h, ← RingHom.ker_eq_comap_bot, hker]
