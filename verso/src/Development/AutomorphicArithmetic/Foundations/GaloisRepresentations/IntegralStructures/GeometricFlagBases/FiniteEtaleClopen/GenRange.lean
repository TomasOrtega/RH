import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FiniteEtaleClopen.ClopenExtAlt

open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open GlobalTheory.GalV (HTower)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Cut

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Rewrite the conclusion using the stated equalities. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
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
