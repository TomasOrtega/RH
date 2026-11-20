import Mathlib
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Set `𝒰` to `Y.affineOpenCover.openCover`. Use `(GlobalTheory.IsNormalScheme.iff_of_openCover (Scheme.Pullback.openCoverOfLeft 𝒰 g (spMap c))).mpr ?_` and prove the remaining obligations. Introduce `i`. Express the relevant statement in the definitionally equal form `GlobalTheory.IsNormalScheme (pullback (𝒰.f i ≫ g) (spMap c))`. Set `R` to `Y.affineOpenCover.X i`.

Establish `hR : GlobalTheory.IsNormalScheme (Spec R)` using `@GlobalTheory.IsNormalScheme.of_isOpenImmersion _ _ (𝒰.f i) (𝒰.map_prop i) hY`. Set `φ` to `Spec.preimage (𝒰.f i ≫ g)`. Use `letI : Algebra F R := φ.hom.toAlgebra`. Use `letI : Algebra F K := c.toAlgebra`. Establish `e1 : 𝒰.f i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F R))` using `(Spec.map_preimage (𝒰.f i ≫ g)).symm`.

Establish `e2 : spMap c = Spec.map (CommRingCat.ofHom (algebraMap F K))` using `rfl`. Rewrite using `[e1, e2]`. Use `(GlobalTheory.IsNormalScheme.iff_of_iso (pullbackSpecIso F R K)).mpr ?_` and prove the remaining obligations. Use `(GlobalTheory.IsNormalScheme.spec_iff _).mpr ?_` and prove the remaining obligations. Conclude with `halg F K R ((GlobalTheory.IsNormalScheme.spec_iff R).mp hR)`.
-/
theorem GlobalTheory.isNormalScheme_pullback_spMap_of_algebra
    (halg : ∀ (F K A : Type) [Field F] [CharZero F] [Field K] [Algebra F K] [CommRing A]
      [Algebra F A], (∀ (P : Ideal A) [P.IsPrime], IsDomain (Localization.AtPrime P) ∧
        IsIntegrallyClosed (Localization.AtPrime P)) →
      ∀ (Q : Ideal (TensorProduct F A K)) [Q.IsPrime], IsDomain (Localization.AtPrime Q) ∧
        IsIntegrallyClosed (Localization.AtPrime Q))
    (F K : Type) [Field F] [CharZero F] [Field K] (c : F →+* K) (Y : Scheme.{0})
    (g : Y ⟶ Sp F) (hY : GlobalTheory.IsNormalScheme Y) : GlobalTheory.IsNormalScheme (pullback g (spMap c)) := by
  let 𝒰 := Y.affineOpenCover.openCover
  refine (GlobalTheory.IsNormalScheme.iff_of_openCover (Scheme.Pullback.openCoverOfLeft 𝒰 g (spMap c))).mpr ?_
  intro i
  change GlobalTheory.IsNormalScheme (pullback (𝒰.f i ≫ g) (spMap c))
  let R := Y.affineOpenCover.X i
  have hR : GlobalTheory.IsNormalScheme (Spec R) :=
    @GlobalTheory.IsNormalScheme.of_isOpenImmersion _ _ (𝒰.f i) (𝒰.map_prop i) hY
  let φ := Spec.preimage (𝒰.f i ≫ g)
  letI : Algebra F R := φ.hom.toAlgebra
  letI : Algebra F K := c.toAlgebra
  have e1 : 𝒰.f i ≫ g = Spec.map (CommRingCat.ofHom (algebraMap F R)) :=
    (Spec.map_preimage (𝒰.f i ≫ g)).symm
  have e2 : spMap c = Spec.map (CommRingCat.ofHom (algebraMap F K)) := rfl
  rw [e1, e2]
  refine (GlobalTheory.IsNormalScheme.iff_of_iso (pullbackSpecIso F R K)).mpr ?_
  refine (GlobalTheory.IsNormalScheme.spec_iff _).mpr ?_
  exact halg F K R ((GlobalTheory.IsNormalScheme.spec_iff R).mp hR)
