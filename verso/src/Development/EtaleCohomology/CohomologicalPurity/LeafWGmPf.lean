import Development.EtaleCohomology.CohomologicalPurity.LeafWEqvLPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.CohomologicalPurity.Thom.ExcP.Chart

/- English proof (translation)
Use `haveI : Algebra.FormallySmooth ℤ (Polynomial ℤ) := Algebra.FormallySmooth.of_equiv (MvPolynomial.pUnitAlgEquiv.{0, 0} ℤ)`. Use `haveI : Algebra.Smooth ℤ (Polynomial ℤ) := ⟨inferInstance, inferInstance⟩`. Conclude with `RingHom.smooth_algebraMap.mpr inferInstance`.
-/
theorem intPoly_smooth : (algebraMap ℤ (Polynomial ℤ)).Smooth := by
  haveI : Algebra.FormallySmooth ℤ (Polynomial ℤ) :=
    Algebra.FormallySmooth.of_equiv (MvPolynomial.pUnitAlgEquiv.{0, 0} ℤ)
  haveI : Algebra.Smooth ℤ (Polynomial ℤ) := ⟨inferInstance, inferInstance⟩
  exact RingHom.smooth_algebraMap.mpr inferInstance

/- English proof (translation)
Establish `h2 : (algebraMap (Polynomial ℤ) (LaurentPolynomial ℤ)).Smooth` using `RingHom.Smooth.holdsForLocalizationAway (LaurentPolynomial ℤ) (Polynomial.X : Polynomial ℤ)`. Use `RingHom.Smooth.comp intPoly_smooth h2` as an intermediate fact. Use `this` and compare the differences between its conclusion and the goal. Conclude with `RingHom.ext_int _ _`.
-/
theorem laurent_smooth : (algebraMap ℤ (LaurentPolynomial ℤ)).Smooth := by
  have h2 : (algebraMap (Polynomial ℤ) (LaurentPolynomial ℤ)).Smooth :=
    RingHom.Smooth.holdsForLocalizationAway (LaurentPolynomial ℤ) (Polynomial.X : Polynomial ℤ)
  have := RingHom.Smooth.comp intPoly_smooth h2
  convert this
  exact RingHom.ext_int _ _

/- English proof (translation)
Establish `e : specZIsTerminal.from Gm = Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ)))` using `specZIsTerminal.hom_ext _ _`. Rewrite using `[e, HasRingHomProperty.Spec_iff (P := @Smooth)]`. Conclude with `laurent_smooth`.
-/
theorem gm_from_smooth : Smooth (specZIsTerminal.from Gm) := by
  have e : specZIsTerminal.from Gm =
      Spec.map (CommRingCat.ofHom (algebraMap ℤ (LaurentPolynomial ℤ))) := specZIsTerminal.hom_ext _ _
  rw [e, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact laurent_smooth

/- English proof (translation)
Establish `hp` using `IsPullback.of_is_product (limit.isLimit (pair X Gm)) specZIsTerminal`. Use `gm_from_smooth` as an intermediate fact. Conclude with `MorphismProperty.of_isPullback (P := @Smooth) hp.flip this`.
-/
theorem gmU_smooth (X : Scheme.{0}) : Smooth (prod.fst : X ⨯ Gm ⟶ X) := by
  have hp := IsPullback.of_is_product (limit.isLimit (pair X Gm)) specZIsTerminal
  have := gm_from_smooth
  exact MorphismProperty.of_isPullback (P := @Smooth) hp.flip this

/- English proof (translation)
Set `pt : Spec (CommRingCat.of ℤ) ⟶ Gm` to `Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1))`. Set `s : X ⟶ X ⨯ Gm` to `prod.lift (𝟙 X) (specZIsTerminal.from X ≫ pt)`. Establish `hs : s ≫ prod.fst = 𝟙 X` using `prod.lift_fst _ _`. Establish `: Surjective (s ≫ prod.fst)` using `by rw [hs]; infer_instance`. Conclude with `Surjective.of_comp s prod.fst`.
-/
theorem gmU_surj (X : Scheme.{0}) : Surjective (prod.fst : X ⨯ Gm ⟶ X) := by
  let pt : Spec (CommRingCat.of ℤ) ⟶ Gm :=
    Spec.map (CommRingCat.ofHom (LaurentPolynomial.eval₂ (RingHom.id ℤ) 1))
  let s : X ⟶ X ⨯ Gm := prod.lift (𝟙 X) (specZIsTerminal.from X ≫ pt)
  have hs : s ≫ prod.fst = 𝟙 X := prod.lift_fst _ _
  have : Surjective (s ≫ prod.fst) := by rw [hs]; infer_instance
  exact Surjective.of_comp s prod.fst

/- English proof (translation)
Introduce `_ _ _ _` and use `⟨gmU_smooth _, gmU_surj _⟩`.
-/
theorem LeafWGm_of : LeafWGm := fun _ _ _ _ => ⟨gmU_smooth _, gmU_surj _⟩

end LateralTheory.CohomologicalPurity.Thom.ExcP.Chart
