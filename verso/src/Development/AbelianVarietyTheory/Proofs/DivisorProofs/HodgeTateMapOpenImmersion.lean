import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PtMapDualBCLeft
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonoFinitePartPullbackStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinitePartPowEqOneLocalStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
open GlobalTheory.FlatModel GlobalTheory.FinPartAt
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FinPartOpen

/- English proof (translation)
Establish `hbij : ∀ x : X, Function.Bijective (f.stalkMap x).hom`. Introduce `x`. Use `⟨?_, f.stalkMap_surjective x⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `h x`. Take `⟨⟨x', φ, hφ⟩, rfl⟩` from `(SpecToEquivOfLocalRing X (Y.presheaf.stalk (f x))).symm.surjective s`.

Rewrite `hs` using `[SpecToEquivOfLocalRing_symm_apply]`. Simplify using `only at hs`. Establish `h1 : f x' = f x`. Use `Scheme.Hom.comp_apply (Spec.map φ ≫ X.fromSpecStalk x') f (IsLocalRing.closedPoint _)` as an intermediate fact. Rewrite `this` using `[hs, Scheme.fromSpecStalk_closedPoint, GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint]`.

Conclude with `this.symm`. Establish `hx : x' = x` using `f.isClosedEmbedding.injective h1`. Substitute `hx` using the available equality. Rewrite `hs` using `[Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc]`. Establish `key : f.stalkMap x' ≫ φ = 𝟙 _`.

Establish `e` using `(SpecToEquivOfLocalRing Y (Y.presheaf.stalk (f x'))).symm.injective (a₁ := ⟨f x', f.stalkMap x' ≫ φ, inferInstance⟩) (a₂ := ⟨f x', 𝟙 _, inferInstance⟩) (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply] dsimp only`. Rewrite using `[hs, Spec.map_id, Category.id_comp])`. Rewrite `e` using `[SpecToEquivOfLocalRing_eq_iff]`. Take `⟨_, e⟩` from `e`. Simplify using `using e`.

Introduce `a b hab`. Use `congrArg φ.hom hab` as an intermediate fact. Rewrite `this` using `[← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key]`. Then use the resulting hypothesis. Establish `: Flat f` using `(Flat.iff_flat_stalkMap f).2 fun x => RingHom.Flat.of_bijective (hbij x)`. Conclude with `IsOpenImmersion.of_flat_of_mono f`.
-/
theorem isOpenImmersion_of_stalk {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f]
    [LocallyOfFinitePresentation f]
    (h : ∀ x : X, ∃ s : Spec (Y.presheaf.stalk (f x)) ⟶ X, s ≫ f = Y.fromSpecStalk (f x)) :
    IsOpenImmersion f := by
  have hbij : ∀ x : X, Function.Bijective (f.stalkMap x).hom := by
    intro x
    refine ⟨?_, f.stalkMap_surjective x⟩
    obtain ⟨s, hs⟩ := h x
    obtain ⟨⟨x', φ, hφ⟩, rfl⟩ := (SpecToEquivOfLocalRing X (Y.presheaf.stalk (f x))).symm.surjective s
    rw [SpecToEquivOfLocalRing_symm_apply] at hs
    dsimp only at hs
    have h1 : f x' = f x := by
      have := Scheme.Hom.comp_apply (Spec.map φ ≫ X.fromSpecStalk x') f (IsLocalRing.closedPoint _)
      rw [hs, Scheme.fromSpecStalk_closedPoint, GlobalTheory.TangentCrit.SpecMap_fromSpecStalk_closedPoint] at this
      exact this.symm
    have hx : x' = x := f.isClosedEmbedding.injective h1
    subst hx
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Spec.map_comp_assoc] at hs
    have key : f.stalkMap x' ≫ φ = 𝟙 _ := by
      have e := (SpecToEquivOfLocalRing Y (Y.presheaf.stalk (f x'))).symm.injective
        (a₁ := ⟨f x', f.stalkMap x' ≫ φ, inferInstance⟩) (a₂ := ⟨f x', 𝟙 _, inferInstance⟩)
        (by rw [SpecToEquivOfLocalRing_symm_apply, SpecToEquivOfLocalRing_symm_apply]
            dsimp only
            rw [hs, Spec.map_id, Category.id_comp])
      rw [SpecToEquivOfLocalRing_eq_iff] at e
      obtain ⟨_, e⟩ := e
      simpa using e
    intro a b hab
    have := congrArg φ.hom hab
    rwa [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, key] at this
  have : Flat f := (Flat.iff_flat_stalkMap f).2 fun x => RingHom.Flat.of_bijective (hbij x)
  exact IsOpenImmersion.of_flat_of_mono f

/- English proof (translation)
Establish `hs : Function.Surjective (f.residueFieldMap x).hom`. Introduce `a`. Take `⟨b, rfl⟩` from `IsLocalRing.residue_surjective a`. Take `⟨c, rfl⟩` from `f.stalkMap_surjective x b`. Conclude with `⟨IsLocalRing.residue _ c, rfl⟩`.

Establish `: IsIso (f.residueFieldMap x)` using `(ConcreteCategory.isIso_iff_bijective _).2 ⟨(f.residueFieldMap x).hom.injective, hs⟩`. Use `⟨Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc, ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]`.
-/
theorem residue_lift {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] (x : X) :
    ∃ s : Spec (Y.residueField (f x)) ⟶ X, s ≫ f = Y.fromSpecResidueField (f x) := by
  have hs : Function.Surjective (f.residueFieldMap x).hom := by
    intro a
    obtain ⟨b, rfl⟩ := IsLocalRing.residue_surjective a
    obtain ⟨c, rfl⟩ := f.stalkMap_surjective x b
    exact ⟨IsLocalRing.residue _ c, rfl⟩
  have : IsIso (f.residueFieldMap x) :=
    (ConcreteCategory.isIso_iff_bijective _).2 ⟨(f.residueFieldMap x).hom.injective, hs⟩
  refine ⟨Spec.map (inv (f.residueFieldMap x)) ≫ X.fromSpecResidueField x, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, ← Category.assoc,
    ← Spec.map_comp, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}} {t : SAB H X}
  {R : Type} [CommRing R] {ξ : Sp R ⟶ X} {q : ℕ} (P' : GlobalTheory.HTMap.FP t ξ q)
  {O : Type} [CommRing O] (x0 : R →+* O) (hu : IsUnit (x0 P'.f))

/- English proof (translation)
Use `haveI := P'.fin.finite`. Conclude with `inferInstanceAs (Module.Finite (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))`.
-/
theorem finite_Bt : Module.Finite O (Bt P' x0 hu) := by
  haveI := P'.fin.finite
  exact inferInstanceAs (Module.Finite (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

/- English proof (translation)
Use `haveI := P'.fin.free`. Conclude with `inferInstanceAs (Module.Free (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))`.
-/
theorem free_Bt : Module.Free O (Bt P' x0 hu) := by
  haveI := P'.fin.free
  exact inferInstanceAs (Module.Free (OL P' x0 hu) (OL P' x0 hu ⊗[Localization.Away P'.f] P'.B))

end

/- English proof (translation)
Introduce `E _ _ _ H X t R _ ξ p _ n _ P' x0 hu P π hg h`. Use `set j := jH P' x0 hu hg.1 h`. Use `haveI := P.semi.separated`. Use `haveI := P.semi.smooth`. Establish `hm : Mono j.left` using `by haveI := GlobalTheory.T.mono_finite_part_pullback P' x0 hu hg.1`.

Establish `e : j.left ≫ (torsion.ι P.G (p ^ n)).left = (aH P' x0 hu hg.1).left`. Rewrite using `[← Over.comp_left, jH_ι]`. Conclude with `mono_of_mono_fac e`. Establish `H0 : IsPullback (torsion.ι P.G (p ^ n)).left (torsion P.G (p ^ n)).hom (mulN P.G (p ^ n)).left η[P.G].left`. Establish `h` using `(IsPullback.of_hasPullback (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).map (Over.forget _)`.

Establish `h' : (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).left = (torsion P.G (p ^ n)).hom` using `(Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)))`. Conclude with `h' ▸ h`. Establish `: LocallyOfFinitePresentation ((mulN P.G (p ^ n)).left ≫ P.G.hom)` using `by rw [Over.w]; infer_instance`. Establish `h3` using `GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp (mulN P.G (p ^ n)).left P.G.hom`. Establish `: IsSeparated ((mulN P.G (p ^ n)).left ≫ P.G.hom)` using `by rw [Over.w]; infer_instance`.

Establish `h4` using `IsSeparated.of_comp (mulN P.G (p ^ n)).left P.G.hom`. Establish `hZlfp : LocallyOfFinitePresentation (torsion P.G (p ^ n)).hom` using `MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H0 h3`. Establish `hZsep : IsSeparated (torsion P.G (p ^ n)).hom` using `MorphismProperty.of_isPullback (P := @IsSeparated) H0 h4`. Use `haveI := finite_Bt P' x0 hu`. Use `haveI := free_Bt P' x0 hu`.

Establish `hHfin : IsFinite (Hs P' x0 hu).hom`. Express the relevant statement in the definitionally equal form `IsFinite (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))`. Rewrite using `[IsFinite.SpecMap_iff]`. Conclude with `RingHom.finite_algebraMap.2 inferInstance`. Establish `hHlfp : LocallyOfFinitePresentation (Hs P' x0 hu).hom`.

Express the relevant statement in the definitionally equal form `LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))`. Rewrite using `[HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]`. Use `haveI : Module.FinitePresentation 𝓞_ℂ_[p] (Bt P' x0 hu) := Module.finitePresentation_of_projective _ _`. Conclude with `RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation _ _)`. Establish `hc : j.left ≫ (torsion P.G (p ^ n)).hom = (Hs P' x0 hu).hom` using `Over.w j`.

Establish `: IsFinite (j.left ≫ (torsion P.G (p ^ n)).hom)` using `by rw [hc]; exact hHfin`. Establish `: LocallyOfFinitePresentation (j.left ≫ (torsion P.G (p ^ n)).hom)` using `by rw [hc]; exact hHlfp`. Establish `: IsFinite j.left` using `IsFinite.of_comp j.left (torsion P.G (p ^ n)).hom`. Establish `: IsClosedImmersion j.left` using `(IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨inferInstance, hm⟩`. Establish `: LocallyOfFinitePresentation j.left` using `GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j.left (torsion P.G (p ^ n)).hom`.

Use `isOpenImmersion_of_stalk j.left fun x => ?_` and prove the remaining obligations. Take `⟨s, hs⟩` from `residue_lift j.left x`. Use `haveI : IsLocalRing ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) := LocallyRingedSpace.isLocalRing _ _`. Conclude with `GlobalTheory.T.finite_part_pow_eq_one_local P' x0 hu hg h ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) (hS := this) ((torsion P.G (p ^ n)).left.fromSpecStalk (j.left x)) ⟨s, hs⟩`.
-/
theorem isOpenImmersion_jH : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (ξ : Sp R ⟶ X) (p : ℕ) [Fact p.Prime] (n : ℕ) [StarRing (𝓞 E)] (P' : GlobalTheory.HTMap.FP t ξ (p ^ n)) (x0 : R →+* 𝓞_ℂ_[p]) (hu : IsUnit (x0 P'.f)) (P : PtP E p) (π : P.G.left ⟶ t.G.left) (hg : IsGrpPullback P.G t.G (spMap x0 ≫ ξ) π) (h : aH P' x0 hu hg.1 ^ (p ^ n) = 1), IsOpenImmersion (jH P' x0 hu hg.1 h).left := by
  intro E _ _ _ H X t R _ ξ p _ n _ P' x0 hu P π hg h
  set j := jH P' x0 hu hg.1 h
  haveI := P.semi.separated
  haveI := P.semi.smooth
  have hm : Mono j.left := by
    haveI := GlobalTheory.T.mono_finite_part_pullback P' x0 hu hg.1
    have e : j.left ≫ (torsion.ι P.G (p ^ n)).left = (aH P' x0 hu hg.1).left := by
      rw [← Over.comp_left, jH_ι]
    exact mono_of_mono_fac e
  have H0 : IsPullback (torsion.ι P.G (p ^ n)).left (torsion P.G (p ^ n)).hom (mulN P.G (p ^ n)).left η[P.G].left := by
    have h := (IsPullback.of_hasPullback (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).map (Over.forget _)
    have h' : (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)).left = (torsion P.G (p ^ n)).hom :=
      (Category.comp_id _).symm.trans (Over.w (pullback.snd (mulN P.G (p ^ n)) (η : 𝟙_ _ ⟶ P.G)))
    exact h' ▸ h
  have : LocallyOfFinitePresentation ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h3 := GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp (mulN P.G (p ^ n)).left P.G.hom
  have : IsSeparated ((mulN P.G (p ^ n)).left ≫ P.G.hom) := by rw [Over.w]; infer_instance
  have h4 := IsSeparated.of_comp (mulN P.G (p ^ n)).left P.G.hom
  have hZlfp : LocallyOfFinitePresentation (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) H0 h3
  have hZsep : IsSeparated (torsion P.G (p ^ n)).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) H0 h4
  haveI := finite_Bt P' x0 hu
  haveI := free_Bt P' x0 hu
  have hHfin : IsFinite (Hs P' x0 hu).hom := by
    change IsFinite (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.2 inferInstance
  have hHlfp : LocallyOfFinitePresentation (Hs P' x0 hu).hom := by
    change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] (Bt P' x0 hu))))
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
    haveI : Module.FinitePresentation 𝓞_ℂ_[p] (Bt P' x0 hu) := Module.finitePresentation_of_projective _ _
    exact RingHom.finitePresentation_algebraMap.2 (Algebra.FinitePresentation.of_finitePresentation _ _)
  have hc : j.left ≫ (torsion P.G (p ^ n)).hom = (Hs P' x0 hu).hom := Over.w j
  have : IsFinite (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHfin
  have : LocallyOfFinitePresentation (j.left ≫ (torsion P.G (p ^ n)).hom) := by rw [hc]; exact hHlfp
  have : IsFinite j.left := IsFinite.of_comp j.left (torsion P.G (p ^ n)).hom
  have : IsClosedImmersion j.left := (IsClosedImmersion.iff_isFinite_and_mono _).2 ⟨inferInstance, hm⟩
  have : LocallyOfFinitePresentation j.left :=
    GlobalTheory.TangentCrit.locallyOfFinitePresentation_of_comp j.left (torsion P.G (p ^ n)).hom
  refine isOpenImmersion_of_stalk j.left fun x => ?_
  obtain ⟨s, hs⟩ := residue_lift j.left x
  haveI : IsLocalRing ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) :=
    LocallyRingedSpace.isLocalRing _ _
  exact GlobalTheory.T.finite_part_pow_eq_one_local P' x0 hu hg h ((torsion P.G (p ^ n)).left.presheaf.stalk (j.left x)) (hS := this)
    ((torsion P.G (p ^ n)).left.fromSpecStalk (j.left x)) ⟨s, hs⟩

end GlobalTheory.FinPartOpen
