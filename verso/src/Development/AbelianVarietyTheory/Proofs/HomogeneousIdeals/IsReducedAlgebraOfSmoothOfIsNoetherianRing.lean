import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.DimSplitPf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

/- English proof (translation)
Set `f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A)` to `Spec.map (CommRingCat.ofHom (algebraMap A B))`. Establish `: Smooth f` using `HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)`. Establish `: GeometricallyReduced f` using `GlobalTheory.geometricallyReduced_of_smooth f`. Establish `: _root_.IsReduced (CommRingCat.of A)` using `inferInstanceAs (_root_.IsReduced A)`. Establish `: IsNoetherianRing (CommRingCat.of A)` using `inferInstanceAs (IsNoetherianRing A)`.

Establish `: IsReduced (Spec (CommRingCat.of B))` using `GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f`. Conclude with `(affine_isReduced_iff (CommRingCat.of B)).mp inferInstance`.
-/
theorem GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [IsNoetherianRing A] [_root_.IsReduced A] :
    _root_.IsReduced B := by

  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : Smooth f := HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : GeometricallyReduced f := GlobalTheory.geometricallyReduced_of_smooth f
  have : _root_.IsReduced (CommRingCat.of A) := inferInstanceAs (_root_.IsReduced A)
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have : IsReduced (Spec (CommRingCat.of B)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  exact (affine_isReduced_iff (CommRingCat.of B)).mp inferInstance

/- English proof (translation)
Take `⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩` from `Algebra.Smooth.exists_subalgebra_fg ℤ A B`. Establish `: Algebra.FiniteType ℤ A₀` using `(Subalgebra.fg_iff_finiteType A₀).mp hfg`. Establish `: IsNoetherianRing A₀` using `Algebra.FiniteType.isNoetherianRing ℤ A₀`. Establish `: Module.Flat A₀ B₀` using `Algebra.Smooth.flat A₀ B₀`. Establish `key : _root_.IsReduced (TensorProduct A₀ B₀ A)`.

Use `IsReduced.tensorProduct_of_flat_of_forall_fg (fun D hD => ?_)` and prove the remaining obligations. Establish `: Algebra.FiniteType A₀ D` using `(Subalgebra.fg_iff_finiteType D).mp hD`. Establish `: IsNoetherianRing D` using `Algebra.FiniteType.isNoetherianRing A₀ D`. Establish `: _root_.IsReduced D` using `isReduced_of_injective D.val Subtype.val_injective`. Establish `: _root_.IsReduced (TensorProduct A₀ D B₀)` using `GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing D (TensorProduct A₀ D B₀)`.

Conclude with `isReduced_of_injective (Algebra.TensorProduct.comm A₀ B₀ D).toRingHom (Algebra.TensorProduct.comm A₀ B₀ D).injective`. Conclude with `isReduced_of_injective ((Algebra.TensorProduct.comm A₀ A B₀).toRingHom.comp e.toRingHom) ((Algebra.TensorProduct.comm A₀ A B₀).injective.comp e.injective)`.
-/
theorem GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [_root_.IsReduced A] :
    _root_.IsReduced B := by

  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : Module.Flat A₀ B₀ := Algebra.Smooth.flat A₀ B₀
  have key : _root_.IsReduced (TensorProduct A₀ B₀ A) := by
    refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun D hD => ?_)
    have : Algebra.FiniteType A₀ D := (Subalgebra.fg_iff_finiteType D).mp hD
    have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A₀ D
    have : _root_.IsReduced D := isReduced_of_injective D.val Subtype.val_injective
    have : _root_.IsReduced (TensorProduct A₀ D B₀) :=
      GlobalTheory.isReduced_algebra_of_smooth_of_isNoetherianRing D (TensorProduct A₀ D B₀)
    exact isReduced_of_injective (Algebra.TensorProduct.comm A₀ B₀ D).toRingHom
      (Algebra.TensorProduct.comm A₀ B₀ D).injective
  exact isReduced_of_injective
    ((Algebra.TensorProduct.comm A₀ A B₀).toRingHom.comp e.toRingHom)
    ((Algebra.TensorProduct.comm A₀ A B₀).injective.comp e.injective)

/- English proof (translation)
Establish `hι : ∀ j, Smooth (Y.affineOpenCover.f j)` using `fun j => inferInstance`. Use `@IsReduced.of_openCover _ Y.affineOpenCover.openCover (fun j => ?_)` and prove the remaining obligations. Establish `h₁ : Smooth (g ≫ T.isoSpec.hom)` using `inferInstance`. Establish `h₂ : Smooth (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom)` using `MorphismProperty.comp_mem _ _ _ (hι j) h₁`. Establish `hs : Smooth (Spec.map (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom)))`.

Rewrite using `[Spec.map_preimage]`. Conclude with `h₂`. Set `` to `(Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom)).hom.toAlgebra`. Establish `: Algebra.Smooth Γ(T, ⊤) (Y.affineOpenCover.X j)` using `HasRingHomProperty.Spec_iff.mp hs`. Establish `: _root_.IsReduced (Y.affineOpenCover.X j)` using `GlobalTheory.isReduced_algebra_of_smooth_of_isReduced Γ(T, ⊤) (Y.affineOpenCover.X j)`.

Use `show IsReduced (Spec (Y.affineOpenCover.X j))`. Use `infer_instance`.
-/
private theorem isReduced_of_smooth_of_isAffine_of_isReduced {Y T : Scheme.{0}} (g : Y ⟶ T) [Smooth g]
    [IsAffine T] [IsReduced T] : IsReduced Y := by
  have hι : ∀ j, Smooth (Y.affineOpenCover.f j) := fun j => inferInstance
  refine @IsReduced.of_openCover _ Y.affineOpenCover.openCover (fun j => ?_)

  have h₁ : Smooth (g ≫ T.isoSpec.hom) := inferInstance
  have h₂ : Smooth (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom) :=
    MorphismProperty.comp_mem _ _ _ (hι j) h₁
  have hs : Smooth (Spec.map (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom))) := by
    rw [Spec.map_preimage]; exact h₂
  let := (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom)).hom.toAlgebra
  have : Algebra.Smooth Γ(T, ⊤) (Y.affineOpenCover.X j) := HasRingHomProperty.Spec_iff.mp hs
  have : _root_.IsReduced (Y.affineOpenCover.X j) :=
    GlobalTheory.isReduced_algebra_of_smooth_of_isReduced Γ(T, ⊤) (Y.affineOpenCover.X j)
  show IsReduced (Spec (Y.affineOpenCover.X j))
  infer_instance

/- English proof (translation)
Establish `hstalk : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x)`. Introduce `x`. Choose the witnesses or unpack the hypotheses as in `⟨V, hV⟩ : ∃ V : S.affineOpens, f x ∈ (V : S.Opens) := by`. Establish `hx : f x ∈ (⨆ V : S.affineOpens, (V : S.Opens))`. Rewrite using `[iSup_affineOpens_eq_top]`.

Discharge the goal by the elementary cases of `trivial`. Simplify `hx` using `[TopologicalSpace.Opens.mem_iSup]`. Establish `: IsAffine (V : S.Opens)` using `V.2`. Establish `hU : IsReduced (f ⁻¹ᵁ (V : S.Opens))` using `isReduced_of_smooth_of_isAffine_of_isReduced (f ∣_ (V : S.Opens))`. Set `y : (f ⁻¹ᵁ (V : S.Opens) : X.Opens)` to `⟨x, hV⟩`.

Use `@isReduced_stalk_of_isReduced _ hU y` as an intermediate fact. Conclude with `isReduced_of_injective (Scheme.Opens.stalkIso _ y).symm.commRingCatIsoToRingEquiv (RingEquiv.injective _)`. Conclude with `isReduced_of_isReduced_stalk X`.
-/
theorem GlobalTheory.isReduced_of_smooth_of_isReduced {X S : Scheme.{0}} (f : X ⟶ S) [Smooth f] [IsReduced S] : IsReduced X := by

  have hstalk : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := by
    intro x
    obtain ⟨V, hV⟩ : ∃ V : S.affineOpens, f x ∈ (V : S.Opens) := by
      have hx : f x ∈ (⨆ V : S.affineOpens, (V : S.Opens)) := by
        rw [iSup_affineOpens_eq_top]; trivial
      simpa [TopologicalSpace.Opens.mem_iSup] using hx
    have : IsAffine (V : S.Opens) := V.2
    have hU : IsReduced (f ⁻¹ᵁ (V : S.Opens)) :=
      isReduced_of_smooth_of_isAffine_of_isReduced (f ∣_ (V : S.Opens))
    let y : (f ⁻¹ᵁ (V : S.Opens) : X.Opens) := ⟨x, hV⟩
    have := @isReduced_stalk_of_isReduced _ hU y
    exact isReduced_of_injective (Scheme.Opens.stalkIso _ y).symm.commRingCatIsoToRingEquiv
      (RingEquiv.injective _)
  exact isReduced_of_isReduced_stalk X
