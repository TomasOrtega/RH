import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsRegularLocalRingOfFlatOfMapEqMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRegularNearOfRegularQuotientPrimeStatement
open IsLocalRing TensorProduct

namespace GlobalTheory

/- English proof (translation)
Establish `hd : Disjoint (q.primeCompl : Set B) (p : Set B)`. Rewrite using `[Set.disjoint_left]`. Introduce `x hx hxp`. Conclude with `hx (hpq hxp)`. Set `P' : Ideal (Localization.AtPrime q)` to `p.map (algebraMap B _)`.

Use `haveI hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hd`. Establish `hc : P'.comap (algebraMap B (Localization.AtPrime q)) = p` using `IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl _ ‹p.IsPrime› hd`. Establish `hsub : (P'.comap (algebraMap B (Localization.AtPrime q))).primeCompl = p.primeCompl`. Use extensionality with `x`. Rewrite using `[Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hc]`.

Use `haveI : IsRegularRing (Localization.AtPrime q) := isRegularRing_of_isRegularLocalRing _`. Establish `hreg : IsRegularLocalRing (Localization.AtPrime P')` using `IsRegularRing.isRegularLocalRing_localization P'`. Use `haveI : IsLocalization p.primeCompl (Localization.AtPrime P') := by`. Rewrite using `[← hsub]`. Conclude with `IsLocalization.isLocalization_atPrime_localization_atPrime q.primeCompl P'`.

Conclude with `IsRegularLocalRing.of_ringEquiv (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime P') (Localization.AtPrime p)).toRingEquiv`.
-/
theorem isRegularLocalRing_atPrime_of_le {B : Type} [CommRing B] (p q : Ideal B) [p.IsPrime]
    [q.IsPrime] (hpq : p ≤ q) (hq : IsRegularLocalRing (Localization.AtPrime q)) :
    IsRegularLocalRing (Localization.AtPrime p) := by
  have hd : Disjoint (q.primeCompl : Set B) (p : Set B) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    exact hx (hpq hxp)
  let P' : Ideal (Localization.AtPrime q) := p.map (algebraMap B _)
  haveI hP' : P'.IsPrime := IsLocalization.isPrime_of_isPrime_disjoint q.primeCompl _ p ‹_› hd
  have hc : P'.comap (algebraMap B (Localization.AtPrime q)) = p :=
    IsLocalization.comap_map_of_isPrime_disjoint q.primeCompl _ ‹p.IsPrime› hd
  have hsub : (P'.comap (algebraMap B (Localization.AtPrime q))).primeCompl = p.primeCompl := by
    ext x
    rw [Ideal.mem_primeCompl_iff, Ideal.mem_primeCompl_iff, hc]
  haveI : IsRegularRing (Localization.AtPrime q) := isRegularRing_of_isRegularLocalRing _
  have hreg : IsRegularLocalRing (Localization.AtPrime P') :=
    IsRegularRing.isRegularLocalRing_localization P'
  haveI : IsLocalization p.primeCompl (Localization.AtPrime P') := by
    rw [← hsub]
    exact IsLocalization.isLocalization_atPrime_localization_atPrime q.primeCompl P'
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv p.primeCompl (Localization.AtPrime P')
      (Localization.AtPrime p)).toRingEquiv

/- English proof (translation)
Introduce `B _ _ hyp`. Apply `GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open B` to reduce the goal to its premises. Introduce `p q hpq hq`. Conclude with `isRegularLocalRing_atPrime_of_le p.asIdeal q.asIdeal hpq hq`. Introduce `p hp`.

Take `⟨g₁, hg₁p, hg₁⟩` from `hyp p.asIdeal`. Take `⟨g₂, hg₂p, hg₂⟩` from `GlobalTheory.T.exists_regular_near_of_regular_quotient_prime B p.asIdeal hp`. Use `⟨g₁ * g₂, fun h => (p.isPrime.mem_or_mem h).elim hg₁p hg₂p, ?_⟩` and prove the remaining obligations. Introduce `q hpq hq`. Establish `hq₁ : g₁ ∉ q.asIdeal` using `fun h => hq (q.asIdeal.mul_mem_right _ h)`.

Establish `hq₂ : g₂ ∉ q.asIdeal` using `fun h => hq (q.asIdeal.mul_mem_left _ h)`. Conclude with `hg₂ q.asIdeal hpq hq₂ (hg₁ q.asIdeal hpq hq₁)`.
-/
theorem isOpen_regularLocus_of_nagata : ∀ (B : Type) [CommRing B] [IsNoetherianRing B], (∀ (p : Ideal B) [p.IsPrime], ∃ g, g ∉ p ∧ ∀ (q : Ideal B) [q.IsPrime], p ≤ q → g ∉ q → IsRegularLocalRing (Localization.AtPrime q ⧸ p.map (algebraMap B (Localization.AtPrime q)))) → IsOpen {Q : PrimeSpectrum B | IsRegularLocalRing (Localization.AtPrime Q.asIdeal)} := by
  intro B _ _ hyp
  apply GlobalTheory.T.isOpen_of_stableUnderGeneralization_of_locally_open B
  · intro p q hpq hq
    exact isRegularLocalRing_atPrime_of_le p.asIdeal q.asIdeal hpq hq
  · intro p hp
    obtain ⟨g₁, hg₁p, hg₁⟩ := hyp p.asIdeal
    obtain ⟨g₂, hg₂p, hg₂⟩ := GlobalTheory.T.exists_regular_near_of_regular_quotient_prime B p.asIdeal hp
    refine ⟨g₁ * g₂, fun h => (p.isPrime.mem_or_mem h).elim hg₁p hg₂p, ?_⟩
    intro q hpq hq
    have hq₁ : g₁ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_right _ h)
    have hq₂ : g₂ ∉ q.asIdeal := fun h => hq (q.asIdeal.mul_mem_left _ h)
    exact hg₂ q.asIdeal hpq hq₂ (hg₁ q.asIdeal hpq hq₁)

end GlobalTheory
