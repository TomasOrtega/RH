import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicHensel.DatExOf

open NumberField IsDedekindDomain UpperTheory.Gal.W2.Seed UpperTheory.Gal.G1 UpperTheory.Gal.Int.Geo GlobalTheory.CongL GlobalTheory.UnitaryBC

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Assume the negation of the conclusion and derive a contradiction. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Move the embeddings inside the algebraic operations. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Move the embeddings inside the algebraic operations. A detailed English derivation is pending.
-/
private theorem intCast_mem_asIdeal_iff_dvd (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))
    (q : ℕ) (hq : q.Prime) (hP : (q : 𝓞 E) ∈ P.asIdeal) (n : ℤ) :
    (n : 𝓞 E) ∈ P.asIdeal ↔ (q : ℤ) ∣ n := by
  constructor
  · intro hn
    by_contra hnd
    have hc : IsCoprime (q : ℤ) n :=
      (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq).irreducible).mpr hnd
    obtain ⟨x, z, hxz⟩ := hc
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one]
    have h1 := congrArg (Int.cast : ℤ → 𝓞 E) hxz
    push_cast at h1
    rw [← h1]
    exact add_mem (Ideal.mul_mem_left _ _ hP) (Ideal.mul_mem_left _ _ hn)
  · rintro ⟨k, rfl⟩
    push_cast
    exact Ideal.mul_mem_right _ _ hP

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities.

Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Use the resulting assumption. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.G1.pKeyK :
    DiscInt → KeyK := by
  intro hD E _ _ _ A q hq hqD r u w hqu hqw hru hrw y hy
  obtain ⟨a, b, hab⟩ := hD E A y hy
  have key : ∀ P : HeightOneSpectrum (𝓞 E), (q : 𝓞 E) ∈ P.asIdeal → A.ω - (r : 𝓞 E) ∈ P.asIdeal →
      (y ∈ P.asIdeal ↔ (q : ℤ) ∣ a + b * r) := by
    intro P hP hωP
    have hDP : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) ∉ P.asIdeal :=
      fun h => hqD ((intCast_mem_asIdeal_iff_dvd E P q hq hP _).mp h)
    have hdiff : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y - ((a + b * r : ℤ) : 𝓞 E) ∈ P.asIdeal := by
      rw [hab]
      have h4 : (a : 𝓞 E) + (b : 𝓞 E) * A.ω - ((a + b * r : ℤ) : 𝓞 E) = (b : 𝓞 E) * (A.ω - (r : 𝓞 E)) := by
        push_cast; ring
      rw [h4]
      exact Ideal.mul_mem_left _ _ hωP
    rw [← intCast_mem_asIdeal_iff_dvd E P q hq hP]
    constructor
    · intro hy'
      have h5 : ((a + b * r : ℤ) : 𝓞 E) = ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y -
          (((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y - ((a + b * r : ℤ) : 𝓞 E)) := by ring
      rw [h5]
      exact sub_mem (Ideal.mul_mem_left _ _ hy') hdiff
    · intro hc
      have hm : ((A.tr ^ 2 - 4 * A.nm : ℤ) : 𝓞 E) * y ∈ P.asIdeal := by
        have h6 := add_mem hdiff hc
        rwa [sub_add_cancel] at h6
      exact (P.isPrime.mem_or_mem hm).resolve_left hDP
  rw [key u hqu hru, key w hqw hrw]
