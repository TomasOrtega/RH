import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointAtZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleLocalizationAtPrimeIsDomainIsIntegrallyClos
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `R C _ _ _ _ M hM`. Take `⟨I, hI⟩` from `(PrimeSpectrum.isClosed_iff_zeroLocus_ideal (Algebra.etaleLocus R C)ᶜ).1 (Algebra.isOpen_etaleLocus (R := R) (A := C)).isClosed_compl`. Distinguish the cases in `hd : Disjoint (I : Set C) (M.map (algebraMap R C) : Set C)`. It suffices to derive a contradiction. Take `⟨Q, hQ, hIQ, hQd⟩` from `Ideal.exists_le_prime_disjoint I (M.map (algebraMap R C)) hd`.

Establish `hE : Algebra.IsEtaleAt R Q`. Use `hM Q fun m hm hmQ => ?_` and prove the remaining obligations. Conclude with `Set.disjoint_left.1 hQd hmQ ⟨m, hm, rfl⟩`. Establish `h1 : (⟨Q, hQ⟩ : PrimeSpectrum C) ∈ Algebra.etaleLocus R C` using `hE`. Establish `h2 : (⟨Q, hQ⟩ : PrimeSpectrum C) ∈ (Algebra.etaleLocus R C)ᶜ`.

Rewrite using `[hI]`. Conclude with `hIQ`. Conclude with `h2 h1`. Rewrite `hd` using `[Set.not_disjoint_iff]`. Take `⟨x, hxI, m, hm, rfl⟩` from `hd`.

Use `⟨m, hm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Algebra.basicOpen_subset_etaleLocus_iff_etale]`. Introduce `p hp`. Assume the negation of the conclusion as `hc`. Establish `: p ∈ (Algebra.etaleLocus R C)ᶜ` using `hc`.

Rewrite `this` using `[hI]`. Conclude with `hp (this hxI)`.
-/
theorem etale_away_of_isEtaleAt_off_submonoid :
  ∀ (R C : Type) [CommRing R] [CommRing C] [Algebra R C] [Algebra.FinitePresentation R C]
    (M : Submonoid R),
    (∀ (Q : Ideal C) [Q.IsPrime], (∀ m ∈ M, algebraMap R C m ∉ Q) → Algebra.IsEtaleAt R Q) →
    ∃ m ∈ M, Algebra.Etale R (Localization.Away (algebraMap R C m)) := by
  intro R C _ _ _ _ M hM
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal (Algebra.etaleLocus R C)ᶜ).1
    (Algebra.isOpen_etaleLocus (R := R) (A := C)).isClosed_compl
  by_cases hd : Disjoint (I : Set C) (M.map (algebraMap R C) : Set C)
  · exfalso
    obtain ⟨Q, hQ, hIQ, hQd⟩ := Ideal.exists_le_prime_disjoint I (M.map (algebraMap R C)) hd
    have hE : Algebra.IsEtaleAt R Q := by
      refine hM Q fun m hm hmQ => ?_
      exact Set.disjoint_left.1 hQd hmQ ⟨m, hm, rfl⟩
    have h1 : (⟨Q, hQ⟩ : PrimeSpectrum C) ∈ Algebra.etaleLocus R C := hE
    have h2 : (⟨Q, hQ⟩ : PrimeSpectrum C) ∈ (Algebra.etaleLocus R C)ᶜ := by
      rw [hI]; exact hIQ
    exact h2 h1
  · rw [Set.not_disjoint_iff] at hd
    obtain ⟨x, hxI, m, hm, rfl⟩ := hd
    refine ⟨m, hm, ?_⟩
    rw [← Algebra.basicOpen_subset_etaleLocus_iff_etale]
    intro p hp
    by_contra hc
    have : p ∈ (Algebra.etaleLocus R C)ᶜ := hc
    rw [hI] at this
    exact hp (this hxI)

end GlobalTheory
