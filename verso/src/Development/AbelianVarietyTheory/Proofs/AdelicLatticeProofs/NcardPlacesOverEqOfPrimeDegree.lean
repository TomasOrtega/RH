import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.MemPowSub
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

/- English proof (translation)
Introduce `p F E _ _ _ _ _ _ hp hdeg v w w' hne hw hw'`. Establish `: IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E)` using `IsGaloisGroup.of_isFractionRing _ _ _ F E`. Establish `hv` using `v.isMaximal`. Establish `himg : (fun u : HeightOneSpectrum (𝓞 E) => u.asIdeal) '' {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} = v.asIdeal.primesOver (𝓞 E)`. Use extensionality with `P`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu, rfl⟩`. Establish `hu' : u.under (𝓞 F) = v` using `hu`. Conclude with `⟨u.isPrime, ⟨by rw [← hu']; rfl⟩⟩`. Introduce and unpack `⟨hP, hPv⟩`.

Use `⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ?_, rfl⟩` and prove the remaining obligations. Conclude with `HeightOneSpectrum.ext hPv.over.symm`. Establish `hcard : Set.ncard {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} = (v.asIdeal.primesOver (𝓞 E)).ncard`. Rewrite using `[← himg, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]`. Establish `hf` using `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 E) (E ≃ₐ[F] E)`.

Rewrite `hf` using `[IsGalois.card_aut_eq_finrank, hdeg, ← hcard]`. Break down `(Nat.dvd_prime hp).1 (Dvd.intro _ hf) with h1 | h1` into its components or cases. It suffices to derive a contradiction. Take `⟨a, ha⟩` from `Set.ncard_eq_one.1 h1`. Establish `h2 : w ∈ {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v}` using `hw`.

Establish `h3 : w' ∈ {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v}` using `hw'`. Rewrite `h2`, `h3` using `[ha]`. Conclude with `hne (h2.trans h3.symm)`. Conclude with `h1`.
-/
theorem ncard_places_over_eq_of_prime_degree :
    ∀ (p : ℕ) (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      [IsGalois F E], p.Prime → Module.finrank F E = p →
      ∀ (v : HeightOneSpectrum (𝓞 F)) (w w' : HeightOneSpectrum (𝓞 E)), w ≠ w' →
        w.under (𝓞 F) = v → w'.under (𝓞 F) = v →
        Set.ncard {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} = p := by
  intro p F E _ _ _ _ _ _ hp hdeg v w w' hne hw hw'
  have : IsGaloisGroup (E ≃ₐ[F] E) (𝓞 F) (𝓞 E) := IsGaloisGroup.of_isFractionRing _ _ _ F E
  have hv := v.isMaximal
  have himg : (fun u : HeightOneSpectrum (𝓞 E) => u.asIdeal) ''
      {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} = v.asIdeal.primesOver (𝓞 E) := by
    ext P
    constructor
    · rintro ⟨u, hu, rfl⟩
      have hu' : u.under (𝓞 F) = v := hu
      exact ⟨u.isPrime, ⟨by rw [← hu']; rfl⟩⟩
    · rintro ⟨hP, hPv⟩
      refine ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, ?_, rfl⟩
      exact HeightOneSpectrum.ext hPv.over.symm
  have hcard : Set.ncard {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v}
      = (v.asIdeal.primesOver (𝓞 E)).ncard := by
    rw [← himg, Set.ncard_image_of_injective _ (fun a b h => HeightOneSpectrum.ext h)]
  have hf := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn v.asIdeal (𝓞 E)
    (E ≃ₐ[F] E)
  rw [IsGalois.card_aut_eq_finrank, hdeg, ← hcard] at hf
  rcases (Nat.dvd_prime hp).1 (Dvd.intro _ hf) with h1 | h1
  · exfalso
    obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
    have h2 : w ∈ {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} := hw
    have h3 : w' ∈ {u : HeightOneSpectrum (𝓞 E) | u.under (𝓞 F) = v} := hw'
    rw [ha] at h2 h3
    exact hne (h2.trans h3.symm)
  · exact h1

end GlobalTheory.CNorm
