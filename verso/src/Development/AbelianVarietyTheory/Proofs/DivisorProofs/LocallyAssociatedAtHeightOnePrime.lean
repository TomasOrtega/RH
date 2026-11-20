import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MemRangeOfForallHeightEqOneOfIsReflexive
open IsLocalRing

namespace GlobalTheory

/- English proof (translation)
Take `⟨y, hy⟩` from `h`. Take `⟨⟨z, s⟩, hs⟩` from `IsLocalization.surj Q.primeCompl y`. Establish `e : algebraMap B (Localization.AtPrime Q) (b * s) = algebraMap B (Localization.AtPrime Q) (a * z)`. Rewrite using `[map_mul, map_mul, hy, mul_assoc, hs]`. Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists Q.primeCompl _).mp e`.

Use `⟨c * s, Q.primeCompl.mul_mem c.2 s.2, c * z, ?_⟩` and prove the remaining obligations. Take the linear combination `hc`.
-/
theorem exists_notMem_dvd_mul_of_algebraMap_dvd {B : Type} [CommRing B] (Q : Ideal B) [Q.IsPrime]
    {a b : B}
    (h : algebraMap B (Localization.AtPrime Q) a ∣ algebraMap B (Localization.AtPrime Q) b) :
    ∃ t ∉ Q, a ∣ t * b := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨⟨z, s⟩, hs⟩ := IsLocalization.surj Q.primeCompl y
  have e : algebraMap B (Localization.AtPrime Q) (b * s) =
      algebraMap B (Localization.AtPrime Q) (a * z) := by
    rw [map_mul, map_mul, hy, mul_assoc, hs]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists Q.primeCompl _).mp e
  refine ⟨c * s, Q.primeCompl.mul_mem c.2 s.2, c * z, ?_⟩
  linear_combination hc

/- English proof (translation)
Establish `hdvr : IsDiscreteValuationRing (Localization.AtPrime (𝔭.map (algebraMap A' B')))` using `isDiscreteValuationRing_of_height_eq_one _ h1 _`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime (𝔭.map (algebraMap A' B')))`. Establish `hm : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) = Ideal.span {ϖ}` using `hϖ.maximalIdeal_eq`. Take `⟨p, hp𝔭, hp⟩ : ∃ p ∈ 𝔭, ¬ ϖ ^ 2 ∣ algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (algebraMap A' B' p)` from `by by_contra! H`. Establish `hle : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) ≤ Ideal.span {ϖ ^ 2}`.

Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]`. Introduce `q hq`. Rewrite using `[Ideal.mem_comap, Ideal.mem_span_singleton]`. Conclude with `H q hq`. Establish `hmem : ϖ ∈ Ideal.span {ϖ ^ 2}` using `hle (hm ▸ Ideal.mem_span_singleton_self ϖ)`.

Rewrite `hmem` using `[Ideal.mem_span_singleton]`. Take `⟨r, hr⟩` from `hmem`. Apply `hϖ.not_isUnit` to reduce the goal to its premises. Use `isUnit_iff_exists_inv.mpr ⟨r, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hϖ.ne_zero` to reduce the goal to its premises.

Rewrite using `[mul_one]`. Take the linear combination `-hr`. Establish `hxm : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (algebraMap A' B' p) ∈ maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B')))`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal]`. Conclude with `Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hp𝔭)`.

Establish `hx0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (algebraMap A' B' p) ≠ 0` using `fun h => hp (h ▸ dvd_zero _)`. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ`. Establish `hn : n = 1`. Break down `n with _ | _ | n` into its components or cases. It suffices to derive a contradiction.

Rewrite `hu` using `[pow_zero, mul_one]`. Conclude with `(mem_maximalIdeal _).mp hxm (hu ▸ u.isUnit)`. Both sides reduce to the same expression. It suffices to derive a contradiction. Apply `hp` to reduce the goal to its premises.

Rewrite using `[hu]`. Conclude with `Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _`. Substitute `hn` using the available equality. Establish `hc0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c ≠ 0`. Introduce `h`.

Apply `hc` to reduce the goal to its premises. Apply `IsLocalization.injective (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (𝔭.map (algebraMap A' B')).primeCompl_le_nonZeroDivisors` to reduce the goal to its premises. Rewrite using `[h, map_zero]`. Take `⟨m, v, hv⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ`. Establish `hass : Associated (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c) (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (algebraMap A' B' (p ^ m)))`.

Rewrite using `[map_pow, map_pow, hu, hv, pow_one, mul_pow]`. Conclude with `(associated_unit_mul_left _ _ v.isUnit).trans (associated_unit_mul_left _ _ (u.isUnit.pow m)).symm`. Conclude with `⟨p ^ m, exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.dvd, exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.symm.dvd⟩`.
-/
theorem exists_locally_associated_algebraMap_of_height_eq_one (A' B' : Type) [CommRing A']
    [CommRing B'] [IsDomain B'] [IsNoetherianRing B'] [IsIntegrallyClosed B'] [Algebra A' B']
    (𝔭 : Ideal A') (hQ : (𝔭.map (algebraMap A' B')).IsPrime)
    (h1 : (𝔭.map (algebraMap A' B')).height = 1) (c : B') (hc : c ≠ 0) :
    ∃ j : A', (∃ t ∉ 𝔭.map (algebraMap A' B'), c ∣ t * algebraMap A' B' j) ∧
      (∃ t ∉ 𝔭.map (algebraMap A' B'), algebraMap A' B' j ∣ t * c) := by
  have hdvr : IsDiscreteValuationRing (Localization.AtPrime (𝔭.map (algebraMap A' B'))) :=
    isDiscreteValuationRing_of_height_eq_one _ h1 _
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible
    (Localization.AtPrime (𝔭.map (algebraMap A' B')))
  have hm : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  obtain ⟨p, hp𝔭, hp⟩ : ∃ p ∈ 𝔭, ¬ ϖ ^ 2 ∣
      algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) (algebraMap A' B' p) := by
    by_contra! H
    have hle : maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) ≤
        Ideal.span {ϖ ^ 2} := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
      intro q hq
      rw [Ideal.mem_comap, Ideal.mem_span_singleton]
      exact H q hq
    have hmem : ϖ ∈ Ideal.span {ϖ ^ 2} := hle (hm ▸ Ideal.mem_span_singleton_self ϖ)
    rw [Ideal.mem_span_singleton] at hmem
    obtain ⟨r, hr⟩ := hmem
    apply hϖ.not_isUnit
    refine isUnit_iff_exists_inv.mpr ⟨r, ?_⟩
    apply mul_left_cancel₀ hϖ.ne_zero
    rw [mul_one]
    linear_combination -hr
  have hxm : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (algebraMap A' B' p) ∈ maximalIdeal (Localization.AtPrime (𝔭.map (algebraMap A' B'))) := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hp𝔭)
  have hx0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (algebraMap A' B' p) ≠ 0 := fun h => hp (h ▸ dvd_zero _)
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ
  have hn : n = 1 := by
    rcases n with _ | _ | n
    · exfalso
      rw [pow_zero, mul_one] at hu
      exact (mem_maximalIdeal _).mp hxm (hu ▸ u.isUnit)
    · rfl
    · exfalso
      apply hp
      rw [hu]
      exact Dvd.dvd.mul_left (pow_dvd_pow ϖ (by omega)) _
  subst hn
  have hc0 : algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c ≠ 0 := by
    intro h
    apply hc
    apply IsLocalization.injective (Localization.AtPrime (𝔭.map (algebraMap A' B')))
      (𝔭.map (algebraMap A' B')).primeCompl_le_nonZeroDivisors
    rw [h, map_zero]
  obtain ⟨m, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hc0 hϖ
  have hass : Associated (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B'))) c)
      (algebraMap B' (Localization.AtPrime (𝔭.map (algebraMap A' B')))
        (algebraMap A' B' (p ^ m))) := by
    rw [map_pow, map_pow, hu, hv, pow_one, mul_pow]
    exact (associated_unit_mul_left _ _ v.isUnit).trans
      (associated_unit_mul_left _ _ (u.isUnit.pow m)).symm
  exact ⟨p ^ m, exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.dvd,
    exists_notMem_dvd_mul_of_algebraMap_dvd _ hass.symm.dvd⟩

end GlobalTheory
