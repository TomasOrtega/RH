import Mathlib
import Development.EtaleCohomology.WeilConjectures.AcycPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace UpperTheory.Cb

open LateralTheory.EWeil.AcycPf

/- English proof (translation)
Set `e : J ≌ ULiftHom.{1} J` to `ULiftHom.equiv`. Use `haveI : IsFiltered (ULiftHom.{1} J) := IsFiltered.of_equivalence e`. Conclude with `HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{1} (ULift.{1} R)) e.symm`.
-/
private lemma exact_filtered (R : Type) [CommRing R] (J : Type 1) [Category.{0} J] [IsFiltered J] :
    HasExactColimitsOfShape J (ModuleCat.{1} (ULift.{1} R)) := by
  let e : J ≌ ULiftHom.{1} J := ULiftHom.equiv
  haveI : IsFiltered (ULiftHom.{1} J) := IsFiltered.of_equivalence e
  exact HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{1} (ULift.{1} R)) e.symm

/- English proof (translation)
Establish `key : m = (hc.coconePointUniqueUpToIso (colimit.isColimit K)).hom ≫ colimMap τ ≫ (hd.coconePointUniqueUpToIso (colimit.isColimit L)).inv`. Use `hc.hom_ext fun j => ?_` and prove the remaining obligations. Simplify using `[hm]`. Establish `hτ : Mono (colim.map τ)` using `inferInstance`. Establish `hτ' : Mono (colimMap τ)` using `hτ`.

Rewrite using `[key]`. Use `infer_instance`.
-/
private lemma mono_of_isColimit {J : Type 1} [Category.{0} J] {A : Type 2} [Category.{1} A] [Abelian A]
    [HasColimitsOfShape J A] [HasExactColimitsOfShape J A] {K L : J ⥤ A} (τ : K ⟶ L) [Mono τ]
    {c : Cocone K} {d : Cocone L} (hc : IsColimit c) (hd : IsColimit d) (m : c.pt ⟶ d.pt)
    (hm : ∀ j, c.ι.app j ≫ m = τ.app j ≫ d.ι.app j) : Mono m := by
  have key : m = (hc.coconePointUniqueUpToIso (colimit.isColimit K)).hom ≫ colimMap τ ≫
      (hd.coconePointUniqueUpToIso (colimit.isColimit L)).inv := by
    refine hc.hom_ext fun j => ?_
    simp [hm]
  have hτ : Mono (colim.map τ) := inferInstance
  have hτ' : Mono (colimMap τ) := hτ
  rw [key]
  infer_instance

/- English proof (translation)
Establish `hφ : ∀ c, Mono (φ.app c)` using `fun c => inferInstance`. Establish `key : ∀ X, Mono (((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X)`. Introduce `X`. Use `haveI : IsFiltered (CostructuredArrow G.op X) := IsFiltered.of_equivalence (structuredArrowOpEquivalence G (unop X))`. Use `haveI := hA (CostructuredArrow G.op X)`.

Use `haveI : ∀ j, Mono ((Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ).app j) := fun j => hφ _`. Use `haveI : Mono (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ) := NatTrans.mono_of_mono_app _`. Use `mono_of_isColimit (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ) (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op P X) (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op Q X) _ ?_` and prove the remaining obligations. Introduce `j`. Establish `h₂ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app (G.op.obj j.left) = φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left` using `(congr_app (G.op.lanUnit.naturality φ) j.left).symm`.

Establish `h₃ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj P).map j.hom ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X = φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj Q).map j.hom`. Rewrite using `[NatTrans.naturality, reassoc_of% h₂]`. Use `first`. Consider the case `exact (Category.assoc _ _ _).trans h₃`. Consider the case `(dsimp only [Functor.LeftExtension.coconeAt_ι_app, Functor.whiskerLeft_app]`.

Simplify `h₃)` using `only [Category.assoc]`. Conclude with `NatTrans.mono_of_mono_app _`.
-/
private lemma lan_mono {C D : Type 1} [Category.{0} C] [Category.{0} D] (G : C ⥤ D) [RepresentablyFlat G]
    {A : Type 2} [Category.{1} A] [Abelian A]
    [∀ X, HasColimitsOfShape (CostructuredArrow G.op X) A]
    (hA : ∀ (J : Type 1) [Category.{0} J] [IsFiltered J] [HasColimitsOfShape J A], HasExactColimitsOfShape J A)
    {P Q : Cᵒᵖ ⥤ A} (φ : P ⟶ Q) [Mono φ] : Mono ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ) := by
  have hφ : ∀ c, Mono (φ.app c) := fun c => inferInstance
  have key : ∀ X, Mono (((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X) := by
    intro X
    haveI : IsFiltered (CostructuredArrow G.op X) :=
      IsFiltered.of_equivalence (structuredArrowOpEquivalence G (unop X))
    haveI := hA (CostructuredArrow G.op X)
    haveI : ∀ j, Mono ((Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ).app j) :=
      fun j => hφ _
    haveI : Mono (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ) :=
      NatTrans.mono_of_mono_app _
    refine mono_of_isColimit (Functor.whiskerLeft (CostructuredArrow.proj G.op X) φ)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op P X)
      (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit G.op Q X) _ ?_
    intro j
    have h₂ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app (G.op.obj j.left) =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left :=
      (congr_app (G.op.lanUnit.naturality φ) j.left).symm
    have h₃ : (G.op.lanUnit.app P).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj P).map j.hom ≫
        ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).map φ).app X =
        φ.app j.left ≫ (G.op.lanUnit.app Q).app j.left ≫ ((G.op.lan : _ ⥤ Dᵒᵖ ⥤ A).obj Q).map j.hom := by
      rw [NatTrans.naturality, reassoc_of% h₂]
    first
      | exact (Category.assoc _ _ _).trans h₃
      | (dsimp only [Functor.LeftExtension.coconeAt_ι_app, Functor.whiskerLeft_app]
         simpa only [Category.assoc] using h₃)
  exact NatTrans.mono_of_mono_app _

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Establish `: PreservesFiniteLimits (incl S)` using `inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget S))`. Conclude with `flat_of_preservesFiniteLimits _`.
-/
private lemma incl_flat (S : Scheme.{0}) : RepresentablyFlat (incl S) := by
  have : PreservesFiniteLimits (incl S) :=
    inferInstanceAs (PreservesFiniteLimits (Scheme.Etale.forget S))
  exact flat_of_preservesFiniteLimits _

set_option backward.isDefEq.respectTransparency false in
/- English proof (translation)
Use `incl_flat S` as an intermediate fact. Use `haveI : (incl S).Full := inferInstanceAs (Scheme.Etale.forget S).Full`. Use `haveI : (incl S).Faithful := inferInstanceAs (Scheme.Etale.forget S).Faithful`. Use `haveI : (incl S).LocallyCoverDense (Scheme.etaleTopology.over S) := Scheme.locallyCoverDense_of_le (P := @Etale) S le_rfl`. Rewrite using `[Functor.isContinuous_iff_coverPreserving]`.

Conclude with `Functor.coverPreserving_restrictedTopology (incl S) (Scheme.etaleTopology.over S)`.
-/
private lemma incl_cont (S : Scheme.{0}) :
    (incl S).IsContinuous S.smallEtaleTopology (Scheme.etaleTopology.over S) := by
  have := incl_flat S
  haveI : (incl S).Full := inferInstanceAs (Scheme.Etale.forget S).Full
  haveI : (incl S).Faithful := inferInstanceAs (Scheme.Etale.forget S).Faithful
  haveI : (incl S).LocallyCoverDense (Scheme.etaleTopology.over S) :=
    Scheme.locallyCoverDense_of_le (P := @Etale) S le_rfl
  rw [Functor.isContinuous_iff_coverPreserving]
  exact Functor.coverPreserving_restrictedTopology (incl S) (Scheme.etaleTopology.over S)

/- English proof (translation)
Introduce `R _ S G _`. Use `haveI := incl_cont S`. Set `adj` to `Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (incl S) (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology (Scheme.etaleTopology.over S)`. Use `haveI : (Functor.sheafPullbackConstruction.sheafPullback (incl S) (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology (Scheme.etaleTopology.over S)).PreservesMonomorphisms := by`. Prove the components needed by the constructor for the conclusion.

Introduce `X Y f hf`. Use `haveI := incl_flat S`. Use `haveI : Mono ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f) := inferInstance`. Use `haveI : Mono (((incl S).op.lan : _ ⥤ (Over S)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)).map ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f)) := lan_mono (incl S) (fun J _ _ _ => exact_filtered R J) _`. Conclude with `(presheafToSheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))).map_mono _`.

Conclude with `⟨(((incl S).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology (Scheme.etaleTopology.over S)).obj G).property, adj.map_injective G inferInstance⟩`.
-/
private lemma restr_inj : RestrInj := by
  intro R _ S G _
  haveI := incl_cont S
  let adj := Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (incl S)
    (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology (Scheme.etaleTopology.over S)
  haveI : (Functor.sheafPullbackConstruction.sheafPullback (incl S) (ModuleCat.{1} (ULift.{1} R))
      S.smallEtaleTopology (Scheme.etaleTopology.over S)).PreservesMonomorphisms := by
    constructor
    intro X Y f hf
    haveI := incl_flat S
    haveI : Mono ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f) :=
      inferInstance
    haveI : Mono (((incl S).op.lan : _ ⥤ (Over S)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} R)).map
        ((sheafToPresheaf S.smallEtaleTopology (ModuleCat.{1} (ULift.{1} R))).map f)) :=
      lan_mono (incl S) (fun J _ _ _ => exact_filtered R J) _
    exact (presheafToSheaf (Scheme.etaleTopology.over S) (ModuleCat.{1} (ULift.{1} R))).map_mono _
  exact ⟨(((incl S).sheafPushforwardContinuous (ModuleCat.{1} (ULift.{1} R)) S.smallEtaleTopology
    (Scheme.etaleTopology.over S)).obj G).property, adj.map_injective G inferInstance⟩

end UpperTheory.Cb

/- English proof (translation)
The claim follows from `UpperTheory.Cb.restr_inj`.
-/
theorem UpperTheory.Cb.restrInj : LateralTheory.EWeil.AcycPf.RestrInj := UpperTheory.Cb.restr_inj
