import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralAtSection
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
/- English proof (translation)
Simplify using `[Functor.grpObjObj, Functor.monObjObj]`. Establish `h` using `pullback.condition (f := 𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)`. Simplify using `only [Category.comp_id] at h`. Use `erw [pullback.lift_fst]`. Rewrite using `[← Category.assoc, ← h]`.
-/
private lemma unit_pullback_left_comp_fst_eq_spMap_comp_unit {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ ≫ η[G].left := by
  simp [Functor.grpObjObj, Functor.monObjObj]
  have h := pullback.condition (f := 𝟙 (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) (g := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)
  simp only [Category.comp_id] at h
  erw [pullback.lift_fst]
  rw [← Category.assoc, ← h]

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in
/- English proof (translation)
Establish `h` using `Over.w (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G])`. Simplify using `using h`.
-/
private lemma unit_pullback_left_comp_snd_eq_id {W R : Type} [CommRing W] [CommRing R] (φ : W →+* R)
    (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] :
    (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G]).left ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = 𝟙 _ := by
  have h := Over.w (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ)).obj G])
  simpa using h

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise in
open IsLocalRing in
attribute [local instance] Over.cartesianMonoidalCategory in

/- English proof (translation)
Introduce `K W K' _ _ _ _ _ A _ G _ e he σ x hx₁ hx₂`. Establish `hxη : x = (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[hx₁, unit_pullback_left_comp_fst_eq_spMap_comp_unit]`. Rewrite using `[hx₂, unit_pullback_left_comp_snd_eq_id]`.

Both sides reduce to the same expression. Establish `hη : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left ≫ e.hom.left = (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left`. Rewrite using `[← Over.comp_left, IsMonHom.one_hom]`. Establish `hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')`. Rewrite using `[_root_.GlobalTheory.spMap_comp_spMap]`.

Use `congr 1`. Use extensionality with `y`. Conclude with `σ.commutes y`. Establish `hinv : e.hom.left ≫ e.inv.left = 𝟙 _`. Rewrite using `[← Over.comp_left, e.hom_inv_id, Over.id_left]`.

Establish `hmap : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left ≫ pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap …`. Apply `pullback.hom_ext` to reduce the goal to its premises. Simplify using `only [Category.assoc, pullback.lift_fst, Category.comp_id]`. Rewrite using `[unit_pullback_left_comp_fst_eq_spMap_comp_unit, ← Category.assoc, hσ]`. Simplify using `only [Category.assoc, pullback.lift_snd]`.

Rewrite using `[← Category.assoc, unit_pullback_left_comp_snd_eq_id]`. Simplify using the standard rewrite rules. Rewrite using `[hxη, ← Category.assoc, hη, ← Category.assoc, hmap, Category.assoc, ← hη, Category.assoc, hinv, Category.comp_id]`.
-/
theorem _root_.GlobalTheory.semilinear_symm_fixes_unit : ∀ (K W K' : Type) [Field K] [CommRing W] [Field K'] [Algebra W K'] [Algebra K K'] (A : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K)) [GrpObj A] (G : Over (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp W)) [GrpObj G] (e : (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G ≅ (Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A), IsMonHom e.hom → ∀ (σ : K' ≃ₐ[K] K') (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K' ⟶ pullback G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))), x ≫ pullback.fst G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K') ≫ η[G].left → x ≫ pullback.snd G.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K')) = 𝟙 _ → x ≫ (e.hom.left ≫ pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _) (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp) (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) ≫ e.inv.left) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ x := by
  intro K W K' _ _ _ _ _ A _ G _ e he σ x hx₁ hx₂

  have hxη : x = (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left := by
    apply pullback.hom_ext
    · rw [hx₁, unit_pullback_left_comp_fst_eq_spMap_comp_unit]
    · rw [hx₂, unit_pullback_left_comp_snd_eq_id]
      rfl
  have hη : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap W K'))).obj G]).left ≫ e.hom.left =
      (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    rw [← Over.comp_left, IsMonHom.one_hom]
  have hσ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K') := by
    rw [_root_.GlobalTheory.spMap_comp_spMap]
    congr 1
    ext y
    exact σ.commutes y
  have hinv : e.hom.left ≫ e.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, e.hom_inv_id, Over.id_left]
  have hmap : (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left ≫
      pullback.map A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) A.hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K')) (𝟙 _)
        (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K')) (𝟙 _) (by simp)
        (by rw [Category.comp_id, ← Spec.map_comp]; congr 1; ext y; exact (σ.commutes y).symm) =
      _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (σ : K' →+* K') ≫ (η[(Over.pullback (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap K K'))).obj A]).left := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.comp_id]
      rw [unit_pullback_left_comp_fst_eq_spMap_comp_unit, ← Category.assoc, hσ]
    · simp only [Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, unit_pullback_left_comp_snd_eq_id]
      simp
  rw [hxη, ← Category.assoc, hη, ← Category.assoc, hmap, Category.assoc, ← hη, Category.assoc,
    hinv, Category.comp_id]

end GlobalTheory
