import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

namespace SecBGeneric

variable {K : Type*} [Field K] [NumberField K]

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac, IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply, MvPolynomial.algebraMap_eq]`.
-/
theorem parToFrac_comp_algebraMap (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) :
    (parToFrac e n v).comp (algebraMap (𝓞 K) (ParDVR e n v)) =
      (kToFrac K e n).comp (algebraMap (𝓞 K) K) := by
  ext x
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply (𝓞 K) (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v), parToFrac,
    IsLocalization.lift_eq, kToFrac, IsFractionRing.lift_algebraMap, RingHom.comp_apply,
    MvPolynomial.algebraMap_eq]

/- English proof (translation)
Rewrite using `[parY, parToFrac, IsLocalization.lift_eq, parYF]`.
-/
theorem parToFrac_parY (e n : ℕ) (v : HeightOneSpectrum (𝓞 K)) (p : Par e n) :
    parToFrac e n v (parY e n v p) = parYF K e n p := by
  rw [parY, parToFrac, IsLocalization.lift_eq, parYF]

/- English proof (translation)
Simplify using `[linForm, map_sum]`.
-/
theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (f : R →+* S) (u : Fin n → R) :
    MvPolynomial.map f (linForm u) = linForm (fun j => f (u j)) := by
  simp [linForm, map_sum]

/- English proof (translation)
Use `le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl) fun f hf => ?_` and prove the remaining obligations. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) f.coeffs`. Establish `hb0 : (algebraMap (𝓞 K) K b) ≠ 0` using `(IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)`. Establish `hrange : C (algebraMap (𝓞 K) K b) * f ∈ Set.range (MvPolynomial.map (algebraMap (𝓞 K) K))`. Rewrite using `[mem_range_map_iff_coeffs_subset]`.

Introduce `x hx`. Take `⟨m, hm, rfl⟩` from `mem_coeffs_iff.mp hx`. Rewrite using `[coeff_C_mul]`. Distinguish the cases in `h0 : coeff m f = 0`. Rewrite using `[h0, mul_zero]`.

Conclude with `⟨0, map_zero _⟩`. Take `⟨y, hy⟩` from `hb _ (coeff_mem_coeffs m h0)`. Conclude with `⟨y, by rw [hy, Algebra.smul_def]⟩`. Take `⟨g, hg⟩` from `hrange`. Establish `hgI : g ∈ integralModel I` using `by show MvPolynomial.map (algebraMap (𝓞 K) K) g ∈ I`.

Rewrite using `[hg]`. Conclude with `I.mul_mem_left _ hf`. Establish `: f = C (algebraMap (𝓞 K) K b)⁻¹ * MvPolynomial.map (algebraMap (𝓞 K) K) g`. Rewrite using `[hg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]`. Rewrite using `[this]`.

Conclude with `Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgI)`.
-/
theorem map_integralModel {n : ℕ} (I : Ideal (MvPolynomial (Fin n) K)) :
    (integralModel I).map (MvPolynomial.map (algebraMap (𝓞 K) K)) = I := by
  refine le_antisymm (Ideal.map_le_iff_le_comap.mpr le_rfl) fun f hf => ?_
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K)) f.coeffs
  have hb0 : (algebraMap (𝓞 K) K b) ≠ 0 :=
    (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2)
  have hrange : C (algebraMap (𝓞 K) K b) * f ∈ Set.range (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro x hx
    obtain ⟨m, hm, rfl⟩ := mem_coeffs_iff.mp hx
    rw [coeff_C_mul]
    by_cases h0 : coeff m f = 0
    · rw [h0, mul_zero]; exact ⟨0, map_zero _⟩
    · obtain ⟨y, hy⟩ := hb _ (coeff_mem_coeffs m h0)
      exact ⟨y, by rw [hy, Algebra.smul_def]⟩
  obtain ⟨g, hg⟩ := hrange
  have hgI : g ∈ integralModel I := by
    show MvPolynomial.map (algebraMap (𝓞 K) K) g ∈ I
    rw [hg]
    exact I.mul_mem_left _ hf
  have : f = C (algebraMap (𝓞 K) K b)⁻¹ * MvPolynomial.map (algebraMap (𝓞 K) K) g := by
    rw [hg, ← mul_assoc, ← C_mul, inv_mul_cancel₀ hb0, C_1, one_mul]
  rw [this]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ hgI)

/- English proof (translation)
Establish `h1 : (modelR e I v).map (MvPolynomial.map (parToFrac e n v)) = idealF e I`. Establish `hc : (MvPolynomial.map (parToFrac e n v)).comp (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) : MvPolynomial (Fin n) (𝓞 K) →+* _) = (MvPolynomial.map (kToFrac K e n)).comp (MvPolynomial.map (algebraMap (𝓞 K) K))`. Use `RingHom.ext fun p => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply, MvPolynomial.map_map, parToFrac_comp_algebraMap]`. Rewrite using `[modelR, Ideal.map_map, hc, ← Ideal.map_map, map_integralModel, idealF]`.

Establish `h2 : (Ideal.span (Set.range (secForm (parY e n v)))).map (MvPolynomial.map (parToFrac e n v)) = Ideal.span (Set.range (secForm (parYF K e n)))`. Rewrite using `[Ideal.map_span, ← Set.range_comp]`. Use `congr 2`. Use function extensionality and compare the values at `i`. Simplify using `only [Function.comp_apply, secForm, map_linForm, parToFrac_parY]`.

Establish `h3 : (Ideal.span {chartForm (parY e n v) - 1}).map (MvPolynomial.map (parToFrac e n v)) = Ideal.span {chartForm (parYF K e n) - 1}`. Rewrite using `[Ideal.map_span, Set.image_singleton, map_sub, map_one, chartForm, chartForm, map_linForm]`. Simplify using `only [parToFrac_parY]`. Rewrite using `[secIdeal, secIdeal, Ideal.map_sup, Ideal.map_sup, h1, h2, h3]`.
-/
theorem map_secIdeal {n : ℕ} (e : ℕ) (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) :
    (secIdeal (modelR e I v) (parY e n v)).map (MvPolynomial.map (parToFrac e n v)) =
      secIdeal (idealF e I) (parYF K e n) := by
  have h1 : (modelR e I v).map (MvPolynomial.map (parToFrac e n v)) = idealF e I := by
    have hc : (MvPolynomial.map (parToFrac e n v)).comp
        (MvPolynomial.map (algebraMap (𝓞 K) (ParDVR e n v)) : MvPolynomial (Fin n) (𝓞 K) →+* _) =
        (MvPolynomial.map (kToFrac K e n)).comp (MvPolynomial.map (algebraMap (𝓞 K) K)) := by
      refine RingHom.ext fun p => ?_
      simp only [RingHom.comp_apply, MvPolynomial.map_map, parToFrac_comp_algebraMap]
    rw [modelR, Ideal.map_map, hc, ← Ideal.map_map, map_integralModel, idealF]
  have h2 : (Ideal.span (Set.range (secForm (parY e n v)))).map (MvPolynomial.map (parToFrac e n v)) =
      Ideal.span (Set.range (secForm (parYF K e n))) := by
    rw [Ideal.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp only [Function.comp_apply, secForm, map_linForm, parToFrac_parY]
  have h3 : (Ideal.span {chartForm (parY e n v) - 1}).map (MvPolynomial.map (parToFrac e n v)) =
      Ideal.span {chartForm (parYF K e n) - 1} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one, chartForm, chartForm, map_linForm]
    simp only [parToFrac_parY]
  rw [secIdeal, secIdeal, Ideal.map_sup, Ideal.map_sup, h1, h2, h3]

end SecBGeneric

open SecBGeneric in

/- English proof (translation)
Introduce `K _ _ n e I v _`. Establish `hJ` using `map_secIdeal e I v`. Set `M : Submonoid (MvPolynomial (Fin n) (ParDVR e n v))` to `(nonZeroDivisors (ParDVR e n v)).map (MvPolynomial.C : ParDVR e n v →+* MvPolynomial (Fin n) (ParDVR e n v))`. Set `φ : SecB e I v →+* SecAlg (idealF e I) (parYF K e n)` to `Ideal.quotientMap _ (MvPolynomial.map (parToFrac e n v)) (hJ ▸ Ideal.le_comap_map)`. Use `⟨φ, fun j => ?_, fun r => ?_, ?_⟩` and prove the remaining obligations.

Simplify using `[φ, secCoord, Ideal.quotientMap_mk]`. Establish `hr : algebraMap (ParDVR e n v) (SecB e I v) r = Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (C r)` using `rfl`. Rewrite using `[hr]`. Simplify using `only [φ, Ideal.quotientMap_mk, map_C]`. Both sides reduce to the same expression.

Set `` to `φ.toAlgebra`. Set `: Algebra (ParDVR e n v) (ParFrac K e n)` to `(parToFrac e n v).toAlgebra`. Establish `: IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n)` using `IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm`. Establish `: IsFractionRing (ParDVR e n v) (ParFrac K e n)` using `IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl _ _`. Set `: Algebra (MvPolynomial (Fin n) (ParDVR e n v)) (MvPolynomial (Fin n) (ParFrac K e n))` to `MvPolynomial.algebraMvPolynomial`.

Use `MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (ParDVR e n v)) (ParFrac K e n)` as an intermediate fact. Establish `key` using `IsLocalization.of_surjective M (MvPolynomial (Fin n) (ParFrac K e n)) (S' := SecAlg (idealF e I) (parYF K e n)) (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) Ideal.Quotient.mk_surjective (Ideal.Quotient.mk (secIdeal (idealF e I) (parYF K e n))) Ideal.Quotient.mk_surj …`. Establish `hM : Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)) = M.map (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)))`. Use extensionality with `x`. Simplify using `only [M, Algebra.algebraMapSubmonoid, Submonoid.mem_map, exists_exists_and_eq_and]`.

Conclude with `Iff.rfl`. Rewrite using `[hM]`. Conclude with `key`.
-/
theorem SecBGeneric.proof : SecBGeneric.Statement := by
  intro K _ _ n e I v _
  have hJ := map_secIdeal e I v
  let M : Submonoid (MvPolynomial (Fin n) (ParDVR e n v)) :=
    (nonZeroDivisors (ParDVR e n v)).map (MvPolynomial.C : ParDVR e n v →+* MvPolynomial (Fin n) (ParDVR e n v))
  let φ : SecB e I v →+* SecAlg (idealF e I) (parYF K e n) :=
    Ideal.quotientMap _ (MvPolynomial.map (parToFrac e n v)) (hJ ▸ Ideal.le_comap_map)
  refine ⟨φ, fun j => ?_, fun r => ?_, ?_⟩
  · simp [φ, secCoord, Ideal.quotientMap_mk]
  · have hr : algebraMap (ParDVR e n v) (SecB e I v) r =
        Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v)) (C r) := rfl
    rw [hr]
    simp only [φ, Ideal.quotientMap_mk, map_C]
    rfl
  let := φ.toAlgebra
  let : Algebra (ParDVR e n v) (ParFrac K e n) := (parToFrac e n v).toAlgebra
  have : IsScalarTower (MvPolynomial (Par e n) (𝓞 K)) (ParDVR e n v) (ParFrac K e n) :=
    IsScalarTower.of_algebraMap_eq' (IsLocalization.lift_comp _).symm
  have : IsFractionRing (ParDVR e n v) (ParFrac K e n) :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (parPrime e n v).primeCompl _ _
  let : Algebra (MvPolynomial (Fin n) (ParDVR e n v)) (MvPolynomial (Fin n) (ParFrac K e n)) :=
    MvPolynomial.algebraMvPolynomial
  have := MvPolynomial.isLocalization (σ := Fin n) (nonZeroDivisors (ParDVR e n v)) (ParFrac K e n)
  have key := IsLocalization.of_surjective M
    (MvPolynomial (Fin n) (ParFrac K e n)) (S' := SecAlg (idealF e I) (parYF K e n))
    (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) Ideal.Quotient.mk_surjective
    (Ideal.Quotient.mk (secIdeal (idealF e I) (parYF K e n))) Ideal.Quotient.mk_surjective
    (Ideal.quotientMap_comp_mk _).symm
    (by rw [Ideal.mk_ker, Ideal.mk_ker, ← hJ]; rfl)
  have hM : Algebra.algebraMapSubmonoid (SecB e I v) (nonZeroDivisors (ParDVR e n v)) =
      M.map (Ideal.Quotient.mk (secIdeal (modelR e I v) (parY e n v))) := by
    ext x
    simp only [M, Algebra.algebraMapSubmonoid, Submonoid.mem_map, exists_exists_and_eq_and]
    exact Iff.rfl
  rw [hM]
  exact key

end

end GroundTheory.Heights₂.Heights.Vertical
