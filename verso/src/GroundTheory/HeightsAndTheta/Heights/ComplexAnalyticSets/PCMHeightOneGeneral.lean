import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightOneGeneral
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLocusOpen
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.PSpecChartQuot
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

/- English proof (translation)
Establish `hJW : J ≤ W` using `le_sup_left.trans hW.1.2`. Establish `hgW : g ∈ W` using `hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))`. Establish `hker : RingHom.ker (Ideal.Quotient.mk J) ≤ W` using `by rwa [Ideal.mk_ker]`. Use `set W' : Ideal (R ⧸ J) := W.map (Ideal.Quotient.mk J) with hW'`. Establish `: W'.IsPrime` using `Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker`.

Establish `hcomap : W'.comap (Ideal.Quotient.mk J) = W`. Rewrite using `[hW', Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]`. Establish `hmem : ∀ a : R, Ideal.Quotient.mk J a ∈ W' ↔ a ∈ W` using `fun a => by`. Rewrite using `[← Ideal.mem_comap, hcomap]`. Establish `hsub : W.primeCompl.map (Ideal.Quotient.mk J) = W'.primeCompl`.

Use extensionality with `x`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Take `⟨b, hb, hba⟩` from `Submonoid.mem_map.mp hx`.

Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk J a ∉ W'`. Rewrite using `[← hba, hmem]`. Conclude with `hb`. Introduce `ha`. Conclude with `Submonoid.mem_map.mpr ⟨a, fun h => ha ((hmem a).mpr h), rfl⟩`.

Establish `hloc : IsLocalization.AtPrime (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) W'`. Establish `h` using `Vertical.SpecChart.isLocalization_quot W J`. Rewrite `h` using `[hsub]`. Conclude with `h`. Establish `: IsLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))` using `IsLocalization.AtPrime.isLocalRing _ W'`.

Establish `: IsDomain (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))` using `IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) (M := W'.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors W')`. Use `set x := algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) (Ideal.Quotient.mk J g) with hx`. Establish `hg0 : Ideal.Quotient.mk J g ≠ 0` using `fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)`. Establish `hx0 : x ≠ 0`. Introduce `h`.

Apply `hg0` to reduce the goal to its premises. Establish `h0 : x = algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) 0`. Rewrite using `[map_zero]`. Conclude with `h`. Conclude with `IsLocalization.injective (S := Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) (M := W'.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors W') h0`.

Establish `hxm : x ∈ IsLocalRing.maximalIdeal (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))`. Rewrite using `[← IsLocalization.AtPrime.map_eq_maximalIdeal W']`. Conclude with `Ideal.mem_map_of_mem _ ((hmem g).mpr hgW)`. Establish `hheight : W'.height = 1`. Use `le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hW) ?_` and prove the remaining obligations.

Rewrite using `[Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]`. Introduce `h`. Apply `hg0` to reduce the goal to its premises. Rewrite using `[← Ideal.mem_bot, ← h]`. Conclude with `(hmem g).mpr hgW`.

Use `{ exists_isWeaklyRegular := ⟨[x], ?_, ?_, ?_⟩ }` and prove the remaining obligations. Introduce `r hr`. Rewrite `hr` using `[List.mem_singleton]`. Rewrite using `[hr]`. Conclude with `hxm`.

Rewrite using `[RingTheory.Sequence.isWeaklyRegular_singleton_iff]`. Introduce `a b hab`. Simplify using `only [smul_eq_mul] at hab`. Conclude with `mul_left_cancel₀ hx0 hab`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height W', hheight]`.

Simplify using the standard rewrite rules.
-/
theorem isCohenMacaulayLocalRing_of_minimalPrimes_sup_span {R : Type*} [CommRing R] [IsNoetherianRing R]
    {J W : Ideal R} {g : R} [J.IsPrime] [W.IsPrime] (hg : g ∉ J)
    (hW : W ∈ (J ⊔ Ideal.span {g}).minimalPrimes) :
    IsCohenMacaulayLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  have hgW : g ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self g))
  have hker : RingHom.ker (Ideal.Quotient.mk J) ≤ W := by rwa [Ideal.mk_ker]
  set W' : Ideal (R ⧸ J) := W.map (Ideal.Quotient.mk J) with hW'
  have : W'.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker
  have hcomap : W'.comap (Ideal.Quotient.mk J) = W := by
    rw [hW', Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, sup_eq_left.mpr hker]
  have hmem : ∀ a : R, Ideal.Quotient.mk J a ∈ W' ↔ a ∈ W := fun a => by
    rw [← Ideal.mem_comap, hcomap]
  have hsub : W.primeCompl.map (Ideal.Quotient.mk J) = W'.primeCompl := by
    ext x
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    constructor
    · intro hx
      obtain ⟨b, hb, hba⟩ := Submonoid.mem_map.mp hx
      change Ideal.Quotient.mk J a ∉ W'
      rw [← hba, hmem]
      exact hb
    · intro ha
      exact Submonoid.mem_map.mpr ⟨a, fun h => ha ((hmem a).mpr h), rfl⟩
  have hloc : IsLocalization.AtPrime (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      W' := by
    have h := Vertical.SpecChart.isLocalization_quot W J
    rw [hsub] at h
    exact h
  have : IsLocalRing (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.AtPrime.isLocalRing _ W'
  have : IsDomain (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl)
      (Ideal.primeCompl_le_nonZeroDivisors W')
  set x := algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
    (Ideal.Quotient.mk J g) with hx
  have hg0 : Ideal.Quotient.mk J g ≠ 0 := fun h => hg (Ideal.Quotient.eq_zero_iff_mem.mp h)
  have hx0 : x ≠ 0 := by
    intro h
    apply hg0
    have h0 : x = algebraMap (R ⧸ J) (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) 0 := by
      rw [map_zero]
      exact h
    exact IsLocalization.injective (S := Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W)))
      (M := W'.primeCompl) (Ideal.primeCompl_le_nonZeroDivisors W') h0
  have hxm : x ∈ IsLocalRing.maximalIdeal
      (Localization.AtPrime W ⧸ J.map (algebraMap R (Localization.AtPrime W))) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal W']
    exact Ideal.mem_map_of_mem _ ((hmem g).mpr hgW)
  have hheight : W'.height = 1 := by
    refine le_antisymm (Ideal.map_height_le_one_of_mem_minimalPrimes hW) ?_
    rw [Order.one_le_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
    intro h
    apply hg0
    rw [← Ideal.mem_bot, ← h]
    exact (hmem g).mpr hgW
  refine { exists_isWeaklyRegular := ⟨[x], ?_, ?_, ?_⟩ }
  · intro r hr
    rw [List.mem_singleton] at hr
    rw [hr]
    exact hxm
  · rw [RingTheory.Sequence.isWeaklyRegular_singleton_iff]
    intro a b hab
    simp only [smul_eq_mul] at hab
    exact mul_left_cancel₀ hx0 hab
  · rw [IsLocalization.AtPrime.ringKrullDim_eq_height W', hheight]
    simp

/- English proof (translation)
Introduce `n J W g hJ hg hW`. Establish `: W.IsPrime` using `hW.1.1`. Establish `hJW : J ≤ W` using `le_sup_left.trans hW.1.2`. Take `⟨f, hfW, hf⟩` from `hopen n J W hJW (isCohenMacaulayLocalRing_of_minimalPrimes_sup_span hg hW)`. Use `⟨f, hfW, fun q hq hfq => ?_⟩` and prove the remaining obligations.

Establish `hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ)` using `fun p hp => RingHom.mem_ker.mpr (hq p hp)`. Conclude with `hf _ (hJW.trans hWq) (fun h => hfq (RingHom.mem_ker.mp h))`.
-/
theorem CMHeightOneGeneral.proof (hopen : CMLocusOpen.Statement) : CMHeightOneGeneral.Statement := by
  intro n J W g hJ hg hW
  have : W.IsPrime := hW.1.1
  have hJW : J ≤ W := le_sup_left.trans hW.1.2
  obtain ⟨f, hfW, hf⟩ := hopen n J W hJW (isCohenMacaulayLocalRing_of_minimalPrimes_sup_span hg hW)
  refine ⟨f, hfW, fun q hq hfq => ?_⟩
  have hWq : W ≤ RingHom.ker (eval q : MvPolynomial (Fin n) ℂ →+* ℂ) := fun p hp =>
    RingHom.mem_ker.mpr (hq p hp)
  exact hf _ (hJW.trans hWq) (fun h => hfq (RingHom.mem_ker.mp h))

end GroundTheory.Heights₂.Heights
