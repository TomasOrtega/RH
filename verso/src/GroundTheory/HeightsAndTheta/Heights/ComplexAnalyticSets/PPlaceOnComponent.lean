import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPlaceOnComponent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StReducedNormalisationPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCurveMinimalPrimeQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

/- English proof (translation)
Establish `hpp : p.IsPrime` using `hp.1.1`. Use `le_antisymm (hR ▸ ringKrullDim_le_of_surjective φ hφ) ?_` and prove the remaining obligations. Take `⟨x, y, hxy⟩` from `Order.one_le_krullDim_iff.1 (le_of_eq hR.symm : (1 : WithBot ℕ∞) ≤ ringKrullDim R)`. Establish `hxm : x.asIdeal < IsLocalRing.maximalIdeal R` using `lt_of_lt_of_le hxy (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)`. Establish `hpm : p < IsLocalRing.maximalIdeal R`.

Use `lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top) fun h ↦ ?_` and prove the remaining obligations. Establish `hpx : p ≤ x.asIdeal` using `hp.2 ⟨x.isPrime, bot_le⟩ (h ▸ hxm.le)`. Conclude with `(lt_of_le_of_lt hpx hxm).ne h`. Establish `hk : ∀ K : Ideal R, p ≤ K → (K.map φ).comap φ = K` using `fun K hK ↦ by`. Rewrite using `[Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.2 hK]`.

Establish `h0 : (p.map φ).IsPrime` using `Ideal.map_isPrime_of_surjective hφ hker.le`. Establish `h1 : ((IsLocalRing.maximalIdeal R).map φ).IsPrime` using `Ideal.map_isPrime_of_surjective hφ (hker.le.trans hpm.le)`. Use `Order.one_le_krullDim_iff.2 ⟨⟨_, h0⟩, ⟨_, h1⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `p.map φ < (IsLocalRing.maximalIdeal R).map φ`. Use `lt_of_le_of_ne (Ideal.map_mono hpm.le) fun h ↦ hpm.ne ?_` and prove the remaining obligations.

Rewrite using `[← hk p le_rfl, h, hk _ hpm.le]`.
-/
theorem ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes {R S : Type*} [CommRing R] [CommRing S]
    [IsLocalRing R] (hR : ringKrullDim R = 1) {p : Ideal R} (hp : p ∈ minimalPrimes R) (φ : R →+* S)
    (hφ : Function.Surjective φ) (hker : RingHom.ker φ = p) : ringKrullDim S = 1 := by
  have hpp : p.IsPrime := hp.1.1
  refine le_antisymm (hR ▸ ringKrullDim_le_of_surjective φ hφ) ?_
  obtain ⟨x, y, hxy⟩ := Order.one_le_krullDim_iff.1 (le_of_eq hR.symm : (1 : WithBot ℕ∞) ≤ ringKrullDim R)
  have hxm : x.asIdeal < IsLocalRing.maximalIdeal R :=
    lt_of_lt_of_le hxy (IsLocalRing.le_maximalIdeal y.isPrime.ne_top)
  have hpm : p < IsLocalRing.maximalIdeal R := by
    refine lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hpp.ne_top) fun h ↦ ?_
    have hpx : p ≤ x.asIdeal := hp.2 ⟨x.isPrime, bot_le⟩ (h ▸ hxm.le)
    exact (lt_of_le_of_lt hpx hxm).ne h
  have hk : ∀ K : Ideal R, p ≤ K → (K.map φ).comap φ = K := fun K hK ↦ by
    rw [Ideal.comap_map_of_surjective' φ hφ, hker, sup_eq_left.2 hK]
  have h0 : (p.map φ).IsPrime := Ideal.map_isPrime_of_surjective hφ hker.le
  have h1 : ((IsLocalRing.maximalIdeal R).map φ).IsPrime :=
    Ideal.map_isPrime_of_surjective hφ (hker.le.trans hpm.le)
  refine Order.one_le_krullDim_iff.2 ⟨⟨_, h0⟩, ⟨_, h1⟩, ?_⟩
  change p.map φ < (IsLocalRing.maximalIdeal R).map φ
  refine lt_of_le_of_ne (Ideal.map_mono hpm.le) fun h ↦ hpm.ne ?_
  rw [← hk p le_rfl, h, hk _ hpm.le]

/- English proof (translation)
Introduce `n I q hrad hdim P`. Establish `: IsReduced (curveLocalRing I q)` using `isReduced_curveLocalRing I q hrad`. Establish `: Nontrivial (curveLocalRing I q)`. Use `not_subsingleton_iff_nontrivial.1 fun h ↦ ?_` and prove the remaining obligations. Rewrite `hdim` using `[ringKrullDim_eq_bot_of_subsingleton]`.

Conclude with `absurd hdim (by decide)`. Establish `: IsLocalRing (curveLocalRing I q)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective`. Take `⟨p, hp, hS⟩` from `h₁ (curveLocalRing I q) P`. Take `⟨J, hJ, hJq, φ, hφ, hker, hφf⟩` from `h₂ n I q p hp`. Take `⟨P', hP'⟩` from `hS (curveLocalRing J q) φ hφ hker`.

Use `⟨J, hJ, hJq, ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes hdim hp φ hφ hker, P', fun f ↦ ?_⟩` and prove the remaining obligations. Establish `e` using `hP' (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)`. Rewrite `e` using `[hφf]`. Conclude with `e`.
-/
theorem PlaceOnComponent.proof (h₁ : ReducedNormalisationPlace.Statement)
    (h₂ : CurveMinimalPrimeQuotient.Statement) : PlaceOnComponent.Statement := by
  intro n I q hrad hdim P
  have : IsReduced (curveLocalRing I q) := isReduced_curveLocalRing I q hrad
  have : Nontrivial (curveLocalRing I q) := by
    refine not_subsingleton_iff_nontrivial.1 fun h ↦ ?_
    rw [ringKrullDim_eq_bot_of_subsingleton] at hdim
    exact absurd hdim (by decide)
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  obtain ⟨p, hp, hS⟩ := h₁ (curveLocalRing I q) P
  obtain ⟨J, hJ, hJq, φ, hφ, hker, hφf⟩ := h₂ n I q p hp
  obtain ⟨P', hP'⟩ := hS (curveLocalRing J q) φ hφ hker
  refine ⟨J, hJ, hJq, ringKrullDim_eq_one_of_surjective_of_ker_mem_minimalPrimes hdim hp φ hφ hker, P', fun f ↦ ?_⟩
  have e := hP' (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f)
  rw [hφf] at e
  exact e

end GroundTheory.Heights₂.Heights
