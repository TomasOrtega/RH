import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOfKaehlerDEqZeroStatement

open TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `p hp k _ _ hk S _ _ _ _ f hf`. Establish `hS : IsIntegrallyClosed S` using `IsIntegrallyClosed.of_localization_maximal fun m _ _ => (isDomain_and_isIntegrallyClosed_atPrime_of_smooth k m _).2`. Establish `hK : KaehlerDifferential.D k (FractionRing S) (algebraMap S (FractionRing S) f) = 0`. Rewrite using `[← KaehlerDifferential.map_D k k S (FractionRing S) f, hf, map_zero]`. Take `⟨h, hh⟩` from `GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero' p k hk (FractionRing S) _ hK`.

Establish `hint : IsIntegral S h` using `IsIntegral.of_pow hp.out.pos (by rw [hh]; exact isIntegral_algebraMap)`. Take `⟨y, rfl⟩` from `IsIntegrallyClosed.isIntegral_iff.mp hint`. Use `⟨y, IsFractionRing.injective S (FractionRing S) ?_⟩` and prove the remaining obligations. Rewrite using `[map_pow, hh]`.
-/
theorem exists_pow_eq_of_kaehlerDifferential_eq_zero_of_smooth_domain :
    ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] [IsAlgClosed k] (hk : (p : k) = 0) (S : Type)
      [CommRing S] [IsDomain S] [Algebra k S] [Algebra.Smooth k S] (f : S),
      KaehlerDifferential.D k S f = 0 → ∃ h : S, h ^ p = f := by
  intro p hp k _ _ hk S _ _ _ _ f hf
  have hS : IsIntegrallyClosed S :=
    IsIntegrallyClosed.of_localization_maximal fun m _ _ =>
      (isDomain_and_isIntegrallyClosed_atPrime_of_smooth k m _).2
  have hK : KaehlerDifferential.D k (FractionRing S) (algebraMap S (FractionRing S) f) = 0 := by
    rw [← KaehlerDifferential.map_D k k S (FractionRing S) f, hf, map_zero]
  obtain ⟨h, hh⟩ := GlobalTheory.T.exists_pow_eq_of_kaehler_D_eq_zero' p k hk (FractionRing S) _ hK
  have hint : IsIntegral S h :=
    IsIntegral.of_pow hp.out.pos (by rw [hh]; exact isIntegral_algebraMap)
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, IsFractionRing.injective S (FractionRing S) ?_⟩
  rw [map_pow, hh]

end GlobalTheory
