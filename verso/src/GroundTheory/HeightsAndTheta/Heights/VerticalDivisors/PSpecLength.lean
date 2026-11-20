import Mathlib
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.IntToFracInjective
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsChart
import GroundTheory.HeightsAndTheta.Heights.VerticalDivisors.StatementsOrd
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Vertical

open MvPolynomial NumberField IsDedekindDomain

noncomputable section

/- English proof (translation)
Establish `: Nontrivial (A ⧸ P)`. Use `⟨⟨0, 1, fun h => ?_⟩⟩` and prove the remaining obligations. Establish `h'` using `congrArg ψ h`. Rewrite `h'` using `[map_zero, map_one]`. Conclude with `zero_ne_one h'`.

Establish `: IsLocalRing (A ⧸ P)` using `IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective`. Use `letI := ψ.toAlgebra`. Establish `: Module.Flat (A ⧸ P) L` using `hflat`. Establish `: IsLocalHom (algebraMap (A ⧸ P) L)`. Use `⟨fun a ha => ?_⟩` and prove the remaining obligations.

Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective a`. Conclude with `(hloc.map_nonunit a ha).map _`. Establish `hq : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk P) = IsLocalRing.maximalIdeal (A ⧸ P)`. Establish `h : (IsLocalRing.maximalIdeal (A ⧸ P)).comap (Ideal.Quotient.mk P) = IsLocalRing.maximalIdeal A` using `IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)`. Rewrite using `[← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]`.

Establish `hmax' : (IsLocalRing.maximalIdeal (A ⧸ P)).map (algebraMap (A ⧸ P) L) = IsLocalRing.maximalIdeal L`. Rewrite using `[← hq, Ideal.map_map]`. Conclude with `hmax`. Establish `key` using `IsLocalRing.length_baseChange (A ⧸ P) L ((A ⧸ P) ⧸ J.map (Ideal.Quotient.mk P))`. Rewrite `key` using `[← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L (J.map (Ideal.Quotient.mk P))).toLinearEquiv.length_eq, hmax']`.

Establish `h1 : Module.length L (L ⧸ IsLocalRing.maximalIdeal L) = 1` using `Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)`. Rewrite `key` using `[h1, mul_one, Ideal.map_map, RingHom.algebraMap_toAlgebra]`. Rewrite using `[key, ← Module.length_eq_of_surjective (S := A) Ideal.Quotient.mk_surjective]`. Conclude with `(DoubleQuot.quotQuotEquivQuotSupₐ A P J).toLinearEquiv.length_eq`.
-/
theorem length_quot_map_of_flat {A L : Type*} [CommRing A] [IsLocalRing A] [CommRing L]
    [IsLocalRing L] (P J : Ideal A) (ψ : A ⧸ P →+* L)
    (hloc : IsLocalHom (ψ.comp (Ideal.Quotient.mk P))) (hflat : ψ.Flat)
    (hmax : (IsLocalRing.maximalIdeal A).map (ψ.comp (Ideal.Quotient.mk P)) =
      IsLocalRing.maximalIdeal L) :
    Module.length L (L ⧸ J.map (ψ.comp (Ideal.Quotient.mk P))) =
      Module.length A (A ⧸ (P ⊔ J)) := by
  have : Nontrivial (A ⧸ P) := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    have h' := congrArg ψ h
    rw [map_zero, map_one] at h'
    exact zero_ne_one h'
  have : IsLocalRing (A ⧸ P) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk P) Ideal.Quotient.mk_surjective
  letI := ψ.toAlgebra
  have : Module.Flat (A ⧸ P) L := hflat
  have : IsLocalHom (algebraMap (A ⧸ P) L) := by
    refine ⟨fun a ha => ?_⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact (hloc.map_nonunit a ha).map _
  have hq : (IsLocalRing.maximalIdeal A).map (Ideal.Quotient.mk P) =
      IsLocalRing.maximalIdeal (A ⧸ P) := by
    have h : (IsLocalRing.maximalIdeal (A ⧸ P)).comap (Ideal.Quotient.mk P) =
        IsLocalRing.maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← h, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hmax' : (IsLocalRing.maximalIdeal (A ⧸ P)).map (algebraMap (A ⧸ P) L) =
      IsLocalRing.maximalIdeal L := by
    rw [← hq, Ideal.map_map]
    exact hmax
  have key := IsLocalRing.length_baseChange (A ⧸ P) L ((A ⧸ P) ⧸ J.map (Ideal.Quotient.mk P))
  rw [← (Algebra.TensorProduct.quotIdealMapEquivTensorQuot L
    (J.map (Ideal.Quotient.mk P))).toLinearEquiv.length_eq, hmax'] at key
  have h1 : Module.length L (L ⧸ IsLocalRing.maximalIdeal L) = 1 :=
    Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, inferInstance, ⟨LinearEquiv.refl _ _⟩⟩)
  rw [h1, mul_one, Ideal.map_map, RingHom.algebraMap_toAlgebra] at key
  rw [key, ← Module.length_eq_of_surjective (S := A) Ideal.Quotient.mk_surjective]
  exact (DoubleQuot.quotQuotEquivQuotSupₐ A P J).toLinearEquiv.length_eq

/- English proof (translation)
Simplify using `only [linForm, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]`.
-/
theorem map_linForm {R S : Type*} [CommRing R] [CommRing S] {n : ℕ} (φ : R →+* S) (u : Fin n → R) :
    (linForm u).map φ = linForm (fun j => φ (u j)) := by
  simp only [linForm, map_sum, map_mul, MvPolynomial.map_C, MvPolynomial.map_X]

/- English proof (translation)
Rewrite using `[secLin, map_linForm]`.
-/
theorem secLin_eq_mk_map {K : Type*} [Field K] [NumberField K] {n e : ℕ}
    (I : Ideal (MvPolynomial (Fin n) K)) (v : HeightOneSpectrum (𝓞 K)) (u : Fin n → 𝓞 K) :
    secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j)) =
      Ideal.Quotient.mk _ ((linForm u).map (algebraMap (𝓞 K) (ParDVR e n v))) := by
  rw [secLin, map_linForm]

/- English proof (translation)
Introduce `K _ _ n e I f u v hI hf hu 𝔫 W hW hWn`. Establish `hWp : W.IsPrime` using `hW.1.1.1`. Take `⟨ψ, hψ, hloc, hflat, hmax⟩` from `h1 K n e I v hI 𝔫 W hW hWn`. Use `h3 K e n v` as an intermediate fact. Use `h4 K n e I f v hI hf` as an intermediate fact.

Establish `hfin` using `h2 (ParDVR e n v) (SecB e I v) _ (h5 K n e I f u v hI hf hu) 𝔫`. Establish `hx : algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal) (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))) = (ψ.comp (Ideal.Quotient.mk _)) (algebraMap _ (Localization.AtPrime W) (linForm u))`. Rewrite using `[RingHom.comp_apply, hψ]`. Conclude with `congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)) (secLin_eq_mk_map I v u)`. Establish `hlen0` using `length_quot_map_of_flat (A := Localization.AtPrime W) (L := Localization.AtPrime 𝔫.asIdeal) (P := (integralModel I).map (algebraMap _ (Localization.AtPrime W))) (J := Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}) (ψ := ψ) hloc hflat`.

Establish `hlen` using `hlen0 hmax`. Rewrite `hlen` using `[Ideal.map_span, Set.image_singleton, ← hx]`. Establish `hmult : localMult (integralModel I ⊔ Ideal.span {linForm u}) W = (Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸ ((integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔ Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}))).toNat`. Rewrite using `[localMult, dif_pos hWp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]`. Unfold `Ring.ord at hfin ⊢`.

Rewrite `hfin`, the goal using `[hlen]`. Use `split_ifs with hlW`. Rewrite using `[hmult, ENat.natCast_toNat hfin]`. Establish `hunit : IsUnit (algebraMap _ (Localization.AtPrime W) (linForm u))` using `(IsLocalization.AtPrime.isUnit_to_map_iff _ W _).mpr hlW`. Establish `htop : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔ Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)} = ⊤` using `eq_top_iff.mpr (le_sup_of_le_right (Ideal.span_singleton_eq_top.mpr hunit).ge)`.

Rewrite using `[htop]`. Establish `: Subsingleton (Localization.AtPrime W ⧸ (⊤ : Ideal (Localization.AtPrime W)))` using `Ideal.Quotient.subsingleton_iff.mpr rfl`. Conclude with `Module.length_eq_zero`.
-/
theorem SpecLength.proof (h1 : SpecChart.Statement) (h2 : FiniteOrd.Statement)
    (h3 : ParDVRIsDVR.Statement) (h4 : SecBFinite.Statement) (h5 : SecBLinInj.Statement) :
    SpecLength.Statement := by
  classical
  intro K _ _ n e I f u v hI hf hu 𝔫 W hW hWn
  have hWp : W.IsPrime := hW.1.1.1
  obtain ⟨ψ, hψ, hloc, hflat, hmax⟩ := h1 K n e I v hI 𝔫 W hW hWn
  have := h3 K e n v
  have := h4 K n e I f v hI hf
  have hfin := h2 (ParDVR e n v) (SecB e I v) _ (h5 K n e I f u v hI hf hu) 𝔫
  have hx : algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)
      (secLin (modelR e I v) (parY e n v) (fun j => algebraMap (𝓞 K) (ParDVR e n v) (u j))) =
      (ψ.comp (Ideal.Quotient.mk _)) (algebraMap _ (Localization.AtPrime W) (linForm u)) := by
    rw [RingHom.comp_apply, hψ]
    exact congrArg (algebraMap (SecB e I v) (Localization.AtPrime 𝔫.asIdeal)) (secLin_eq_mk_map I v u)
  have hlen0 := length_quot_map_of_flat (A := Localization.AtPrime W)
    (L := Localization.AtPrime 𝔫.asIdeal)
    (P := (integralModel I).map (algebraMap _ (Localization.AtPrime W)))
    (J := Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}) (ψ := ψ) hloc hflat
  have hlen := hlen0 hmax
  rw [Ideal.map_span, Set.image_singleton, ← hx] at hlen
  have hmult : localMult (integralModel I ⊔ Ideal.span {linForm u}) W =
      (Module.length (Localization.AtPrime W) (Localization.AtPrime W ⧸
        ((integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
          Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)}))).toNat := by
    rw [localMult, dif_pos hWp, Ideal.map_sup, Ideal.map_span, Set.image_singleton]
  unfold Ring.ord at hfin ⊢
  rw [hlen] at hfin ⊢
  split_ifs with hlW
  · rw [hmult, ENat.natCast_toNat hfin]
  · have hunit : IsUnit (algebraMap _ (Localization.AtPrime W) (linForm u)) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff _ W _).mpr hlW
    have htop : (integralModel I).map (algebraMap _ (Localization.AtPrime W)) ⊔
        Ideal.span {algebraMap _ (Localization.AtPrime W) (linForm u)} = ⊤ :=
      eq_top_iff.mpr (le_sup_of_le_right (Ideal.span_singleton_eq_top.mpr hunit).ge)
    rw [htop]
    have : Subsingleton (Localization.AtPrime W ⧸ (⊤ : Ideal (Localization.AtPrime W))) :=
      Ideal.Quotient.subsingleton_iff.mpr rfl
    exact Module.length_eq_zero

end

end GroundTheory.Heights₂.Heights.Vertical
