import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsSecIdealOfPrime
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

/- English proof (translation)
The claim follows from `Ideal.map_map _ _`.
-/
theorem secIdealOf_eq_map (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (W : Ideal (MvPolynomial (Fin n) (𝓞 K))) : secIdealOf e I v W = W.map (toSecB e I v) :=
  Ideal.map_map _ _

/- English proof (translation)
Simplify using `only [toSecB, RingHom.comp_apply, MvPolynomial.map_C]`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Both sides reduce to the same expression.
-/
theorem toSecB_C (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (a : 𝓞 K) :
    toSecB e I v (C a) = algebraMap (ParDVR e n v) (SecB e I v)
      (algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a)) := by
  simp only [toSecB, RingHom.comp_apply, MvPolynomial.map_C]
  rw [← IsScalarTower.algebraMap_apply]
  rfl

omit [NumberField K] in
/- English proof (translation)
The claim follows from `(IsLocalization.AtPrime.to_map_mem_maximal_iff (ParDVR e n v) (parPrime e n v) _).mpr (Ideal.mem_map_of_mem _ ha)`.
-/
theorem mem_maximalIdeal_of_mem (e : ℕ) (v : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K} (ha : a ∈ v.asIdeal) :
    algebraMap (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (C a) ∈
      IsLocalRing.maximalIdeal (ParDVR e n v) :=
  (IsLocalization.AtPrime.to_map_mem_maximal_iff (ParDVR e n v) (parPrime e n v) _).mpr (Ideal.mem_map_of_mem _ ha)

/- English proof (translation)
Use `by_contra! h`. Apply `hJ` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one]`. Establish `h1 : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1`. Rewrite using `[← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)`. Rewrite using `[← h1, chartForm, linForm, map_sum]`. Use `J.sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Use `J.mul_mem_left _ ?_` and prove the remaining obligations.

Simplify `h j` using `[toSecB]`.
-/
theorem exists_secCoord_not_mem (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K))
    (J : Ideal (SecB e I v)) (hJ : J ≠ ⊤) : ∃ j, toSecB e I v (X j) ∉ J := by
  by_contra! h
  apply hJ
  rw [Ideal.eq_top_iff_one]
  have h1 : Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (chartForm (parY e n v)) = 1 := by
    rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk _), ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)
  rw [← h1, chartForm, linForm, map_sum]
  refine J.sum_mem fun j _ => ?_
  rw [map_mul]
  refine J.mul_mem_left _ ?_
  simpa [toSecB] using h j

/- English proof (translation)
Introduce `K _ _ n e I f v hI hf`. Use `h1 K n e I f v hI hf` as an intermediate fact. Establish `hcomp : ∀ W ∈ specComps I v, integralModel I ⊔ Ideal.map C v.asIdeal ≤ W` using `fun W hW => hW.1.1.2`. Establish `hmax : ∀ W ∈ specComps I v, (secIdealOf e I v W).IsMaximal`. Introduce `W hW`.

Take `⟨hprime, -⟩` from `h2 K n e I f v hI hf W hW`. Use `Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ParDVR e n v) _ ?_` and prove the remaining obligations. Establish `hle : IsLocalRing.maximalIdeal (ParDVR e n v) ≤ (secIdealOf e I v W).comap (algebraMap (ParDVR e n v) (SecB e I v))`. Rewrite using `[← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]`. Express the relevant statement in the definitionally equal form `Ideal.map C v.asIdeal ≤ _`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Simplify using `only [Ideal.mem_comap]`. Rewrite using `[← toSecB_C, secIdealOf_eq_map]`. Conclude with `Ideal.mem_map_of_mem _ (hcomp W hW (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha)))`.

Rewrite using `[← (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) hle]`. Conclude with `IsLocalRing.maximalIdeal.isMaximal _`. Use `⟨hmax, fun 𝔫 h𝔫 => ?_⟩` and prove the remaining obligations. Use `set W' := 𝔫.comap (toSecB e I v) with hW'`. Establish `hR : 𝔫.comap (algebraMap (ParDVR e n v) (SecB e I v)) = IsLocalRing.maximalIdeal _` using `IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)`.

Establish `hle : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W'`. Use `sup_le (fun p hp => ?_) ?_` and prove the remaining obligations. Establish `h0 : toSecB e I v p = 0` using `Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)))`. Rewrite using `[hW', Ideal.mem_comap, h0]`. Conclude with `𝔫.zero_mem`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Rewrite using `[Ideal.mem_comap, hW', Ideal.mem_comap, toSecB_C, ← Ideal.mem_comap, hR]`. Conclude with `mem_maximalIdeal_of_mem e v ha`. Take `⟨W, hWmin, hWle⟩` from `Ideal.exists_minimalPrimes_le (J := W') hle`.

Take `⟨j, hj⟩` from `exists_secCoord_not_mem e I v 𝔫 h𝔫.ne_top`. Establish `hW : W ∈ specComps I v` using `⟨hWmin, ⟨j, fun h => hj (hWle h)⟩⟩`. Establish `heq : secIdealOf e I v W = 𝔫`. Use `(hmax W hW).eq_of_le h𝔫.ne_top ?_` and prove the remaining obligations. Rewrite using `[secIdealOf_eq_map, Ideal.map_le_iff_le_comap]`.

Conclude with `hWle`. Use `⟨W, ⟨hW, heq⟩, fun W₁ ⟨hW₁, heq₁⟩ => ?_⟩` and prove the remaining obligations. Rewrite using `[← (h2 K n e I f v hI hf W₁ hW₁).2, ← (h2 K n e I f v hI hf W hW).2, heq, heq₁]`.
-/
theorem SpecMax.proof (h1 : SecBFinite.Statement) (h2 : SecIdealOfPrime.Statement) : SpecMax.Statement := by
  intro K _ _ n e I f v hI hf
  have := h1 K n e I f v hI hf
  have hcomp : ∀ W ∈ specComps I v, integralModel I ⊔ Ideal.map C v.asIdeal ≤ W := fun W hW => hW.1.1.2

  have hmax : ∀ W ∈ specComps I v, (secIdealOf e I v W).IsMaximal := by
    intro W hW
    obtain ⟨hprime, -⟩ := h2 K n e I f v hI hf W hW
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_comap (R := ParDVR e n v) _ ?_
    have hle : IsLocalRing.maximalIdeal (ParDVR e n v) ≤
        (secIdealOf e I v W).comap (algebraMap (ParDVR e n v) (SecB e I v)) := by
      rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_le_iff_le_comap]
      change Ideal.map C v.asIdeal ≤ _
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      simp only [Ideal.mem_comap]
      rw [← toSecB_C, secIdealOf_eq_map]
      exact Ideal.mem_map_of_mem _ (hcomp W hW (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ha)))
    rw [← (IsLocalRing.maximalIdeal.isMaximal _).eq_of_le (Ideal.comap_ne_top _ hprime.ne_top) hle]
    exact IsLocalRing.maximalIdeal.isMaximal _
  refine ⟨hmax, fun 𝔫 h𝔫 => ?_⟩

  set W' := 𝔫.comap (toSecB e I v) with hW'
  have hR : 𝔫.comap (algebraMap (ParDVR e n v) (SecB e I v)) = IsLocalRing.maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal _)
  have hle : integralModel I ⊔ Ideal.map C v.asIdeal ≤ W' := by
    refine sup_le (fun p hp => ?_) ?_
    · have h0 : toSecB e I v p = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_left (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ hp)))
      rw [hW', Ideal.mem_comap, h0]
      exact 𝔫.zero_mem
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      rw [Ideal.mem_comap, hW', Ideal.mem_comap, toSecB_C, ← Ideal.mem_comap, hR]
      exact mem_maximalIdeal_of_mem e v ha
  obtain ⟨W, hWmin, hWle⟩ := Ideal.exists_minimalPrimes_le (J := W') hle
  obtain ⟨j, hj⟩ := exists_secCoord_not_mem e I v 𝔫 h𝔫.ne_top
  have hW : W ∈ specComps I v := ⟨hWmin, ⟨j, fun h => hj (hWle h)⟩⟩
  have heq : secIdealOf e I v W = 𝔫 := by
    refine (hmax W hW).eq_of_le h𝔫.ne_top ?_
    rw [secIdealOf_eq_map, Ideal.map_le_iff_le_comap]
    exact hWle
  refine ⟨W, ⟨hW, heq⟩, fun W₁ ⟨hW₁, heq₁⟩ => ?_⟩
  rw [← (h2 K n e I f v hI hf W₁ hW₁).2, ← (h2 K n e I f v hI hf W hW).2, heq, heq₁]

end

end GroundTheory.Heights₂.Heights.Vertical
