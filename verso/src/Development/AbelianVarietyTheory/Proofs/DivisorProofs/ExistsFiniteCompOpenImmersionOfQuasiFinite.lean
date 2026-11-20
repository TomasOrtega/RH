import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetAwayMapSubalgebraBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteCoequifiberedSubalgebraStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelSpecMapIsIsoOverBasicOpenStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizationBasicOpenCoverStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapBijectiveOfRangeEqSubalgebraStatement

open AlgebraicGeometry CategoryTheory Limits Scheme.AffineZariskiSite
namespace GlobalTheory.ZMTFin

/- English proof (translation)
Use `haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected := Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..`. Use `haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected := Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..`. Set `η : (relativeGluingData hα).functor ⟶ (relativeGluingData hα').functor` to `{ app V := Spec.map (ι.app (Opposite.op V)) naturality U V i := by dsimp [relativeGluingData]`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`.

Conclude with `(ι.naturality i.op).symm }`. Use `⟨colimMap η, ?_, ?_⟩` and prove the remaining obligations. Apply `colimit.hom_ext` to reduce the goal to its premises. Introduce `V`. Rewrite using `[ι_colimMap_assoc, Scheme.Cover.RelativeGluingData.ι_toBase, Scheme.Cover.RelativeGluingData.ι_toBase]`.

Substitute `hι` using the available equality. Use `show Spec.map (ι.app _) ≫ (Spec.map (α'.app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι = (Spec.map ((α' ≫ ι).app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι`. Rewrite using `[NatTrans.comp_app, Spec.map_comp]`. Conclude with `(Category.assoc _ _ _).symm`. Introduce `V`.

Conclude with `ι_colimMap η V`.
-/
theorem exists_glued_map (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α) :
    ∃ g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued,
      g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase ∧
      ∀ V, (relativeGluingData hα).cover.f V ≫ g =
        Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V := by
  haveI : ((relativeGluingData hα).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : ((relativeGluingData hα').functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  let η : (relativeGluingData hα).functor ⟶ (relativeGluingData hα').functor :=
    { app V := Spec.map (ι.app (Opposite.op V))
      naturality U V i := by
        dsimp [relativeGluingData]
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        exact (ι.naturality i.op).symm }
  refine ⟨colimMap η, ?_, ?_⟩
  · apply colimit.hom_ext; intro V
    rw [ι_colimMap_assoc, Scheme.Cover.RelativeGluingData.ι_toBase, Scheme.Cover.RelativeGluingData.ι_toBase]
    subst hι
    show Spec.map (ι.app _) ≫ (Spec.map (α'.app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι =
      (Spec.map ((α' ≫ ι).app (Opposite.op V)) ≫ (restrictIsoSpec X).inv.app V) ≫ (V.1).ι
    rw [NatTrans.comp_app, Spec.map_comp]; exact (Category.assoc _ _ _).symm
  · intro V
    exact ι_colimMap η V

/- English proof (translation)
Set `𝒰` to `Scheme.Opens.iSupOpenCover W`. Use `(IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_` and prove the remaining obligations. Use `(MorphismProperty.arrow_mk_iso_iff (.isomorphisms _) ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_` and prove the remaining obligations. Establish `: Scheme.Opens.ι _ ''ᵁ (𝒰.f x).opensRange = W x`. Simplify using `only [Scheme.Opens.iSupOpenCover, 𝒰, ← Scheme.Hom.opensRange_comp, Scheme.homOfLE_ι, Scheme.Opens.opensRange_ι]`.

Use `convert! hW x`.
-/
theorem isIso_morphismRestrict_iSup {Z T : Scheme.{0}} (g : Z ⟶ T) {ι : Type} (W : ι → T.Opens)
    (hW : ∀ i, IsIso (g ∣_ W i)) : IsIso (g ∣_ ⨆ i, W i) := by
  let 𝒰 := Scheme.Opens.iSupOpenCover W
  refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr fun x ↦ ?_
  refine (MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
    ((morphismRestrictRestrict ..).symm ≪≫ morphismRestrictOpensRange ..)).mp ?_
  have : Scheme.Opens.ι _ ''ᵁ (𝒰.f x).opensRange = W x := by
    simp only [Scheme.Opens.iSupOpenCover, 𝒰, ← Scheme.Hom.opensRange_comp, Scheme.homOfLE_ι, Scheme.Opens.opensRange_ι]
  convert! hW x

/- English proof (translation)
Set `h' : U ⟶ (g ⁻¹ᵁ W).toScheme` to `IsOpenImmersion.lift (g ⁻¹ᵁ W).ι h (by simpa using hr)`. Establish `e : h = h' ≫ (g ⁻¹ᵁ W).ι` using `(IsOpenImmersion.lift_fac _ _ _).symm`. Establish `: IsOpenImmersion (h' ≫ (g ⁻¹ᵁ W).ι)` using `by rw [← e]; infer_instance`. Establish `: IsOpenImmersion h'` using `IsOpenImmersion.of_comp h' (g ⁻¹ᵁ W).ι`. Rewrite using `[e, Category.assoc, ← morphismRestrict_ι]`.

Use `infer_instance`.
-/
theorem isOpenImmersion_comp_of_isIso_restrict {U Z T : Scheme.{0}} (h : U ⟶ Z) (g : Z ⟶ T)
    (W : T.Opens) [IsOpenImmersion h] (hg : IsIso (g ∣_ W)) (hr : Set.range h ⊆ (g ⁻¹ᵁ W : Set Z)) :
    IsOpenImmersion (h ≫ g) := by
  let h' : U ⟶ (g ⁻¹ᵁ W).toScheme := IsOpenImmersion.lift (g ⁻¹ᵁ W).ι h (by simpa using hr)
  have e : h = h' ≫ (g ⁻¹ᵁ W).ι := (IsOpenImmersion.lift_fac _ _ _).symm
  have : IsOpenImmersion (h' ≫ (g ⁻¹ᵁ W).ι) := by rw [← e]; infer_instance
  have : IsOpenImmersion h' := IsOpenImmersion.of_comp h' (g ⁻¹ᵁ W).ι
  rw [e, Category.assoc, ← morphismRestrict_ι]
  infer_instance

/- English proof (translation)
Use `haveI : ((relativeGluingData h).functor ⋙ Scheme.forget).IsLocallyDirected := Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..`. Rewrite using `[IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]`. Introduce `U`. Set `V0 : X.AffineZariskiSite` to `⟨U.1, U.2⟩`. Use `haveI : IsOpenImmersion ((relativeGluingData h).cover.f V0) := (relativeGluingData h).cover.map_prop V0`.

Establish `hpre : (relativeGluingData h).toBase ⁻¹ᵁ U.1 = ((relativeGluingData h).cover.f V0).opensRange`. Simplify using `using! (relativeGluingData h).toBase_preimage_eq_opensRange_ι V0`. Set `e` to `IsOpenImmersion.isoOfRangeEq ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre])`. Establish `hU : IsAffineOpen U.1` using `U.2`. Use `haveI : Mono hU.fromSpec := inferInstance`.

Establish `key : e.inv ≫ ((relativeGluingData h).toBase ∣_ U.1) ≫ hU.isoSpec.hom = Spec.map (α'.app (Opposite.op V0))`. Apply `(cancel_mono hU.fromSpec).mp` to reduce the goal to its premises. Use `(relativeGluingData h).ι_toBase V0` as an intermediate fact. Simplify using `[IsAffineOpen.isoSpec_hom, e]`. Use `(congrArg (· ≫ (relativeGluingData h).toBase) (IsOpenImmersion.isoOfRangeEq_inv_fac ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre]))).trans ?_` and prove the remaining obligations.

Use `this.trans ?_` and prove the remaining obligations. Use `show (Spec.map (α'.app (Opposite.op V0)) ≫ hU.isoSpec.inv) ≫ U.1.ι = _`. Conclude with `(Category.assoc _ _ _).trans (congrArg (Spec.map (α'.app (Opposite.op V0)) ≫ ·) (IsAffineOpen.isoSpec_inv_ι hU))`. Rewrite using `[← MorphismProperty.cancel_left_of_respectsIso P e.inv, ← MorphismProperty.cancel_right_of_respectsIso P _ hU.isoSpec.hom, Category.assoc, key]`. Conclude with `hP _`.
-/
theorem toBase_of_Spec (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (P : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget P]
    (hP : ∀ V, P (Spec.map (α'.app V))) : P (relativeGluingData h).toBase := by
  haveI : ((relativeGluingData h).functor ⋙ Scheme.forget).IsLocallyDirected :=
    Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  rw [IsZariskiLocalAtTarget.iff_of_iSup_eq_top (P := P) _ (iSup_affineOpens_eq_top _)]
  intro U
  let V0 : X.AffineZariskiSite := ⟨U.1, U.2⟩
  haveI : IsOpenImmersion ((relativeGluingData h).cover.f V0) := (relativeGluingData h).cover.map_prop V0
  have hpre : (relativeGluingData h).toBase ⁻¹ᵁ U.1 =
      ((relativeGluingData h).cover.f V0).opensRange := by
    simpa using! (relativeGluingData h).toBase_preimage_eq_opensRange_ι V0
  let e := IsOpenImmersion.isoOfRangeEq ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι
    ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre])
  have hU : IsAffineOpen U.1 := U.2
  haveI : Mono hU.fromSpec := inferInstance
  have key : e.inv ≫ ((relativeGluingData h).toBase ∣_ U.1) ≫ hU.isoSpec.hom =
      Spec.map (α'.app (Opposite.op V0)) := by
    apply (cancel_mono hU.fromSpec).mp
    have := (relativeGluingData h).ι_toBase V0
    simp [IsAffineOpen.isoSpec_hom, e]
    refine (congrArg (· ≫ (relativeGluingData h).toBase) (IsOpenImmersion.isoOfRangeEq_inv_fac ((relativeGluingData h).toBase ⁻¹ᵁ U.1).ι ((relativeGluingData h).cover.f V0) (by rw [Scheme.Opens.range_ι, ← Scheme.Hom.coe_opensRange, ← hpre]))).trans ?_
    refine this.trans ?_
    show (Spec.map (α'.app (Opposite.op V0)) ≫ hU.isoSpec.inv) ≫ U.1.ι = _
    exact (Category.assoc _ _ _).trans (congrArg (Spec.map (α'.app (Opposite.op V0)) ≫ ·) (IsAffineOpen.isoSpec_inv_ι hU))
  rw [← MorphismProperty.cancel_left_of_respectsIso P e.inv,
    ← MorphismProperty.cancel_right_of_respectsIso P _ hU.isoSpec.hom, Category.assoc, key]
  exact hP _

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Rewrite using `[IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]`. Conclude with `⟨toBase_of_Spec X F' α' h (@IsIntegralHom : MorphismProperty Scheme.{0}) fun V ↦ IsIntegralHom.SpecMap_iff.mpr (hfin V).to_isIntegral, toBase_of_Spec X F' α' h (@LocallyOfFiniteType : MorphismProperty Scheme.{0}) fun V ↦ (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).m …`.
-/
theorem isFinite_toBase (X : Scheme.{0}) (F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F') (h : α'.Coequifibered)
    (hfin : ∀ V, (α'.app V).hom.Finite) : IsFinite (relativeGluingData h).toBase := by
  rw [IsFinite.iff_isIntegralHom_and_locallyOfFiniteType]
  exact ⟨toBase_of_Spec X F' α' h (@IsIntegralHom : MorphismProperty Scheme.{0}) fun V ↦ IsIntegralHom.SpecMap_iff.mpr (hfin V).to_isIntegral,
    toBase_of_Spec X F' α' h (@LocallyOfFiniteType : MorphismProperty Scheme.{0}) fun V ↦
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr (hfin V).finiteType⟩

/- English proof (translation)
The claim follows from `GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt X F F' α α' hα hα' ι hι g hg₁ hg₂ V b hb W hW`.
-/
theorem isIso_restrict_basicOpen (X : Scheme.{0}) (F F' : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (α' : (toOpensFunctor X).op ⋙ X.presheaf ⟶ F')
    (hα : α.Coequifibered) (hα' : α'.Coequifibered) (ι : F' ⟶ F) (hι : α' ≫ ι = α)
    (g : (relativeGluingData hα).glued ⟶ (relativeGluingData hα').glued)
    (hg₁ : g ≫ (relativeGluingData hα').toBase = (relativeGluingData hα).toBase)
    (hg₂ : ∀ V, (relativeGluingData hα).cover.f V ≫ g =
      Spec.map (ι.app (Opposite.op V)) ≫ (relativeGluingData hα').cover.f V)
    (V : X.AffineZariskiSite) (b : F'.obj (Opposite.op V))
    (hb : Function.Bijective (Localization.awayMap (ι.app (Opposite.op V)).hom b))
    (W : (relativeGluingData hα').glued.Opens)
    (hW : (W : Set (relativeGluingData hα').glued) =
      (relativeGluingData hα').cover.f V '' (PrimeSpectrum.basicOpen b : Set (PrimeSpectrum (F'.obj (Opposite.op V))))) :
    IsIso (g ∣_ W) ∧ ((g ⁻¹ᵁ W : (relativeGluingData hα).glued.Opens) : Set (relativeGluingData hα).glued) =
      (relativeGluingData hα).cover.f V '' (PrimeSpectrum.basicOpen ((ι.app (Opposite.op V)).hom b) :
        Set (PrimeSpectrum (F.obj (Opposite.op V)))) :=
  GlobalTheory.T.relSpec_map_isIso_over_basicOpen_alt X F F' α α' hα hα' ι hι g hg₁ hg₂ V b hb W hW

/- English proof (translation)
The claim follows from `GlobalTheory.T.normalization_basicOpen_cover' U X f V`.
-/
theorem exists_basicOpen_cover (U X : Scheme.{0}) (f : U ⟶ X) (h₁ : IsSeparated f)
    (h₂ : LocallyOfFiniteType f) (h₃ : QuasiCompact f) (h₄ : LocallyQuasiFinite f)
    (V : X.AffineZariskiSite) :
    ∃ G : Finset (f.normalizationDiagram.obj (Opposite.op V.1)),
      (∀ b ∈ G, letI := (f.normalizationDiagramMap.app (Opposite.op V.1)).hom.toAlgebra
        Algebra.FiniteType Γ(X, V.1) (Localization.Away b)) ∧
      ∀ x : U, f x ∈ V.1 → ∃ b ∈ G, f.toNormalization x ∈
        f.normalizationOpenCover.f V '' (PrimeSpectrum.basicOpen b :
          Set (PrimeSpectrum (f.normalizationDiagram.obj (Opposite.op V.1)))) :=
  GlobalTheory.T.normalization_basicOpen_cover' U X f V

/- English proof (translation)
The claim follows from `GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra R A B C φ hφ hC a b hab h`.
-/
theorem bijective_awayMap_of_range (R A B : Type) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R B] (C : Subalgebra R B) (φ : A →+* B) (hφ : Function.Injective φ)
    (hC : ∀ x, x ∈ C ↔ ∃ y, φ y = x) (a : A) (b : B) (hab : φ a = b)
    (h : ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C))) :
    Function.Bijective (Localization.awayMap φ a) :=
  GlobalTheory.T.awayMap_bijective_of_injective_of_range_eq_subalgebra R A B C φ hφ hC a b hab h

set_option backward.isDefEq.respectTransparency false in

/- English proof (translation)
Introduce `U X f hX h₁ h₂ h₃ h₄`. Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t : Finset X.affineOpens, ∀ x : X, ∃ W ∈ t, x ∈ (W : X.Opens) := by`. Take `⟨t, ht⟩` from `(isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover (fun W : X.affineOpens ↦ ((W : X.Opens) : Set X)) (fun W ↦ (W : X.Opens).2) (fun x _ ↦ by`. Take `⟨_, ⟨W, hW, rfl⟩, hxW, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Conclude with `Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)`.

Conclude with `⟨t, fun x ↦ by simpa using ht (Set.mem_univ x)⟩`. Set `n` to `t.card`. Set `V : Fin n → X.AffineZariskiSite` to `fun k ↦ ⟨(t.equivFin.symm k).1.1, (t.equivFin.symm k).1.2⟩`. Establish `hV : ∀ x : X, ∃ k, x ∈ (V k).1` using `fun x ↦ by`. Take `⟨W, hWt, hxW⟩` from `ht x`.

Conclude with `⟨t.equivFin ⟨W, hWt⟩, by simpa [V] using hxW⟩`. Use `choose G hGfin hGcov using fun k ↦ exists_basicOpen_cover U X f h₁ h₂ h₃ h₄ (V k)`. Establish `hs : ∀ k, ∃ s : Finset (f.normalizationDiagram.obj (Opposite.op (V k).1)), (G k : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ s ∧`. Use `letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra`. Use the proof step `∀ C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)), (s : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) → ∀ b ∈ G k, ∀ hb : b ∈ C, Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by`.

Introduce `k`. Use `letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra`. Conclude with `GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge _ _ (G k) (hGfin k)`. Use `choose s hGs hsC using hs`. Establish `hint : ∀ W : X.Opens, IsAffineOpen W → (f.normalizationDiagramMap.app (Opposite.op W)).hom.IsIntegral`.

Introduce `W _`. Use `letI := (f.app W).hom.toAlgebra`. Express the relevant statement in the definitionally equal form `(algebraMap Γ(X, W) (integralClosure Γ(X, W) Γ(U, f ⁻¹ᵁ W))).IsIntegral`. Conclude with `algebraMap_isIntegral_iff.mpr inferInstance`. Take `⟨F', α', ι, hα', hι, hιinj, hfin, hιS⟩` from `GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt X hX f.normalizationDiagram f.normalizationDiagramMap f.coequifibered_normalizationDiagramMap hint n V s`.

Take `⟨g, hg₁, hg₂⟩` from `exists_glued_map X _ F' _ α' f.coequifibered_normalizationDiagramMap hα' ι hι`. Use `⟨_, (relativeGluingData hα').toBase, f.toNormalization ≫ g, isFinite_toBase X F' α' hα' hfin, ?_, ?_⟩` and prove the remaining obligations. Use `rotate_left`. Rewrite using `[Category.assoc, hg₁]`. Conclude with `f.toNormalization_fromNormalization`.

Use `choose b' hb' using fun (k : Fin n) (b : G k) ↦ hιS k b.1 (hGs k b.2)`. Use `haveI : ∀ k, IsOpenImmersion ((relativeGluingData hα').cover.f (V k)) := fun k ↦ (relativeGluingData hα').cover.map_prop _`. Set `Wp : (Σ k, G k) → (relativeGluingData hα').glued.Opens` to `fun p ↦ (relativeGluingData hα').cover.f (V p.1) ''ᵁ PrimeSpectrum.basicOpen (b' p.1 p.2)`. Establish `hbij : ∀ p : Σ k, G k, Function.Bijective (Localization.awayMap (ι.app (Opposite.op (V p.1))).hom (b' p.1 p.2))`. Introduce and unpack `⟨k, b⟩`.

Use `letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra`. Set `C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1))` to `{ (ι.app (Opposite.op (V k))).hom.range with algebraMap_mem' := fun r ↦ ⟨(α'.app (Opposite.op (V k))).hom r, by`. Rewrite using `[← CommRingCat.comp_apply, ← NatTrans.comp_app, hι]`. Use the proof step `rfl⟩ }`. Establish `hsub : ((s k : Finset _) : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _)` using `fun x hx ↦ by obtain ⟨y, hy⟩ := hιS k x hx; exact ⟨y, hy⟩`.

Establish `hC : ∀ x, x ∈ C ↔ ∃ y, (ι.app (Opposite.op (V k))).hom y = x` using `fun x ↦ Iff.rfl`. Establish `hB` using `hsC k C hsub b.1 b.2`. Establish `hφ : Function.Injective (ι.app (Opposite.op (V k))).hom` using `hιinj _`. Conclude with `bijective_awayMap_of_range Γ(X, (V k).1) (F'.obj (Opposite.op (V k))) (f.normalizationDiagram.obj (Opposite.op (V k).1)) C (ι.app _).hom hφ hC (b' k b) b.1 (hb' k b) hB`. Establish `hiso` using `fun p : Σ k, G k ↦ isIso_restrict_basicOpen X _ F' _ α' f.coequifibered_normalizationDiagramMap hα' ι hι g hg₁ hg₂ (V p.1) (b' p.1 p.2) (hbij p) (Wp p) rfl`.

Use `isOpenImmersion_comp_of_isIso_restrict f.toNormalization g (⨆ p, Wp p) (isIso_morphismRestrict_iSup g Wp fun p ↦ (hiso p).1) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨k, hk⟩` from `hV (f x)`. Take `⟨b, hbG, hxb⟩` from `hGcov k x hk`. Establish `h2` using `(hiso ⟨k, ⟨b, hbG⟩⟩).2`.

Rewrite `h2` using `[hb' k ⟨b, hbG⟩]`. Establish `h3 : f.toNormalization x ∈ SetLike.coe (g ⁻¹ᵁ Wp ⟨k, ⟨b, hbG⟩⟩)` using `by rw [h2]; exact hxb`. Conclude with `g.preimage_mono (le_iSup Wp ⟨k, ⟨b, hbG⟩⟩) h3`.
-/
theorem exists_finite_openImmersion : ∀ (U X : Scheme.{0}) (f : U ⟶ X), IsNoetherian X →
    IsSeparated f → LocallyOfFiniteType f → QuasiCompact f → LocallyQuasiFinite f →
    ∃ (T : Scheme.{0}) (q : T ⟶ X) (j : U ⟶ T), IsFinite q ∧ IsOpenImmersion j ∧ j ≫ q = f := by
  intro U X f hX h₁ h₂ h₃ h₄
  obtain ⟨t, ht⟩ : ∃ t : Finset X.affineOpens, ∀ x : X, ∃ W ∈ t, x ∈ (W : X.Opens) := by
    obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (Set.univ : Set X)).elim_finite_subcover
      (fun W : X.affineOpens ↦ ((W : X.Opens) : Set X)) (fun W ↦ (W : X.Opens).2) (fun x _ ↦ by
        obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ :=
          X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
        exact Set.mem_iUnion.mpr ⟨⟨W, hW⟩, hxW⟩)
    exact ⟨t, fun x ↦ by simpa using ht (Set.mem_univ x)⟩
  let n := t.card
  let V : Fin n → X.AffineZariskiSite := fun k ↦ ⟨(t.equivFin.symm k).1.1, (t.equivFin.symm k).1.2⟩
  have hV : ∀ x : X, ∃ k, x ∈ (V k).1 := fun x ↦ by
    obtain ⟨W, hWt, hxW⟩ := ht x
    exact ⟨t.equivFin ⟨W, hWt⟩, by simpa [V] using hxW⟩
  choose G hGfin hGcov using fun k ↦ exists_basicOpen_cover U X f h₁ h₂ h₃ h₄ (V k)
  have hs : ∀ k, ∃ s : Finset (f.normalizationDiagram.obj (Opposite.op (V k).1)),
      (G k : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ s ∧
      letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
      ∀ C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)),
        (s : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) → ∀ b ∈ G k, ∀ hb : b ∈ C,
          Function.Bijective (Localization.awayMap C.val.toRingHom (⟨b, hb⟩ : C)) := by
    intro k
    letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
    exact GlobalTheory.T.exists_finset_awayMap_bijective_of_subalgebra_ge _ _ (G k) (hGfin k)
  choose s hGs hsC using hs
  have hint : ∀ W : X.Opens, IsAffineOpen W →
      (f.normalizationDiagramMap.app (Opposite.op W)).hom.IsIntegral := by
    intro W _
    letI := (f.app W).hom.toAlgebra
    change (algebraMap Γ(X, W) (integralClosure Γ(X, W) Γ(U, f ⁻¹ᵁ W))).IsIntegral
    exact algebraMap_isIntegral_iff.mpr inferInstance
  obtain ⟨F', α', ι, hα', hι, hιinj, hfin, hιS⟩ := GlobalTheory.T.exists_finite_coequifibered_subalgebra_alt X hX f.normalizationDiagram
    f.normalizationDiagramMap f.coequifibered_normalizationDiagramMap hint n V s
  obtain ⟨g, hg₁, hg₂⟩ := exists_glued_map X _ F' _ α' f.coequifibered_normalizationDiagramMap hα' ι hι
  refine ⟨_, (relativeGluingData hα').toBase, f.toNormalization ≫ g,
    isFinite_toBase X F' α' hα' hfin, ?_, ?_⟩
  rotate_left
  · rw [Category.assoc, hg₁]; exact f.toNormalization_fromNormalization
  choose b' hb' using fun (k : Fin n) (b : G k) ↦ hιS k b.1 (hGs k b.2)
  haveI : ∀ k, IsOpenImmersion ((relativeGluingData hα').cover.f (V k)) :=
    fun k ↦ (relativeGluingData hα').cover.map_prop _
  let Wp : (Σ k, G k) → (relativeGluingData hα').glued.Opens := fun p ↦
    (relativeGluingData hα').cover.f (V p.1) ''ᵁ PrimeSpectrum.basicOpen (b' p.1 p.2)
  have hbij : ∀ p : Σ k, G k, Function.Bijective
      (Localization.awayMap (ι.app (Opposite.op (V p.1))).hom (b' p.1 p.2)) := by
    rintro ⟨k, b⟩
    letI := (f.normalizationDiagramMap.app (Opposite.op (V k).1)).hom.toAlgebra
    let C : Subalgebra Γ(X, (V k).1) (f.normalizationDiagram.obj (Opposite.op (V k).1)) :=
      { (ι.app (Opposite.op (V k))).hom.range with
        algebraMap_mem' := fun r ↦ ⟨(α'.app (Opposite.op (V k))).hom r, by
          rw [← CommRingCat.comp_apply, ← NatTrans.comp_app, hι]; rfl⟩ }
    have hsub : ((s k : Finset _) : Set (f.normalizationDiagram.obj (Opposite.op (V k).1))) ⊆ (C : Set _) :=
      fun x hx ↦ by obtain ⟨y, hy⟩ := hιS k x hx; exact ⟨y, hy⟩
    have hC : ∀ x, x ∈ C ↔ ∃ y, (ι.app (Opposite.op (V k))).hom y = x := fun x ↦ Iff.rfl
    have hB := hsC k C hsub b.1 b.2
    have hφ : Function.Injective (ι.app (Opposite.op (V k))).hom := hιinj _
    exact bijective_awayMap_of_range Γ(X, (V k).1) (F'.obj (Opposite.op (V k)))
      (f.normalizationDiagram.obj (Opposite.op (V k).1)) C (ι.app _).hom hφ hC (b' k b) b.1
      (hb' k b) hB
  have hiso := fun p : Σ k, G k ↦ isIso_restrict_basicOpen X _ F' _ α'
    f.coequifibered_normalizationDiagramMap hα' ι hι g hg₁ hg₂ (V p.1) (b' p.1 p.2) (hbij p)
    (Wp p) rfl
  refine isOpenImmersion_comp_of_isIso_restrict f.toNormalization g (⨆ p, Wp p)
    (isIso_morphismRestrict_iSup g Wp fun p ↦ (hiso p).1) ?_
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk⟩ := hV (f x)
  obtain ⟨b, hbG, hxb⟩ := hGcov k x hk
  have h2 := (hiso ⟨k, ⟨b, hbG⟩⟩).2
  rw [hb' k ⟨b, hbG⟩] at h2
  have h3 : f.toNormalization x ∈ SetLike.coe (g ⁻¹ᵁ Wp ⟨k, ⟨b, hbG⟩⟩) := by rw [h2]; exact hxb
  exact g.preimage_mono (le_iSup Wp ⟨k, ⟨b, hbG⟩⟩) h3

end GlobalTheory.ZMTFin
