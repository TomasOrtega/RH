import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLength

noncomputable section

namespace UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B`. Use `haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal`. Use `letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _`. Establish `hb : Function.Bijective (algebraMap κ (B ⧸ p.asIdeal))` using `IsAlgClosed.algebraMap_bijective_of_isIntegral`. Set `e` to `AlgEquiv.ofBijective (Algebra.ofId κ (B ⧸ p.asIdeal)) hb`.

Use `⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[κ] κ).comp (Ideal.Quotient.mkₐ κ p.asIdeal), ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal`. Simplify using `[RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]`.
-/
private theorem exists_algHom_ker (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B]
    [Module.Finite κ B] (p : PrimeSpectrum B) :
    ∃ ε : B →ₐ[κ] κ, RingHom.ker ε.toRingHom = p.asIdeal := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
  letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
  have hb : Function.Bijective (algebraMap κ (B ⧸ p.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := AlgEquiv.ofBijective (Algebra.ofId κ (B ⧸ p.asIdeal)) hb
  refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[κ] κ).comp (Ideal.Quotient.mkₐ κ p.asIdeal), ?_⟩
  ext x
  change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

/- English proof (translation)
Introduce `κ B _ _ _ _ _ ε₀ _ hτ`. Use `haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B`. Use `haveI hfin : Module.Finite κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) := Module.Finite.of_surjective (Algebra.algHom κ B (Localization.AtPrime (RingHom.ker ε₀.toRingHom))).toLinearMap (IsArtinianRing.localization_surjective (RingHom.ker ε₀.toRingHom).primeCompl (Localiza …`. Establish `hm : ∀ p : PrimeSpectrum B, Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = (Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) : ℕ∞)`. Introduce `p`.

Take `⟨ε, hε⟩` from `exists_algHom_ker κ B p`. Take `⟨τ, hτε⟩` from `hτ ε`. Rewrite using `[GlobalTheory.FinSchemeRank.finrank_eq_length_of_isLocalRing κ]`. Establish `hmap : p.asIdeal.primeCompl.map τ.toRingEquiv.toMonoidHom = (RingHom.ker ε₀.toRingHom).primeCompl`. Use extensionality with `y`.

Simplify using `only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, ← hε, RingHom.mem_ker, ← hτε]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `hx`. Introduce `hy`.

Use `⟨τ.symm y, ?_, ?_⟩` and prove the remaining obligations. Simplify using `using hy`. Simplify using the standard rewrite rules. Conclude with `GlobalTheory.FinSchemeRank.length_self_eq_of_ringEquiv (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p.asIdeal) (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) τ.toRingEquiv hmap)`. Establish `h` using `GlobalTheory.FinSchemeRank.finrank_eq_card_mul κ B _ hm`.

Rewrite `h` using `[← GlobalTheory.FinSchemeRank.card_algHom_eq_card_primeSpectrum κ B]`. Conclude with `h` after adjusting the coercions.
-/
theorem ringHomog_of : RingHomog := by
  intro κ B _ _ _ _ _ ε₀ _ hτ
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI hfin : Module.Finite κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) :=
    Module.Finite.of_surjective
      (Algebra.algHom κ B (Localization.AtPrime (RingHom.ker ε₀.toRingHom))).toLinearMap
      (IsArtinianRing.localization_surjective (RingHom.ker ε₀.toRingHom).primeCompl
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)))
  have hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) =
        (Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) : ℕ∞) := by
    intro p
    obtain ⟨ε, hε⟩ := exists_algHom_ker κ B p
    obtain ⟨τ, hτε⟩ := hτ ε
    rw [GlobalTheory.FinSchemeRank.finrank_eq_length_of_isLocalRing κ]
    have hmap : p.asIdeal.primeCompl.map τ.toRingEquiv.toMonoidHom =
        (RingHom.ker ε₀.toRingHom).primeCompl := by
      ext y
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, ← hε, RingHom.mem_ker, ← hτε]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        refine ⟨τ.symm y, ?_, ?_⟩
        · simpa using hy
        · simp
    exact GlobalTheory.FinSchemeRank.length_self_eq_of_ringEquiv
      (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) τ.toRingEquiv hmap)
  have h := GlobalTheory.FinSchemeRank.finrank_eq_card_mul κ B _ hm
  rw [← GlobalTheory.FinSchemeRank.card_algHom_eq_card_primeSpectrum κ B] at h
  exact_mod_cast h

end UpperTheory.Gal.crystallineComparison.Mod
