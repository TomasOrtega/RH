import Development.EtaleCohomology.EtaleSheaves.LeafSHNbSys

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafInj0Pf LateralTheory.E.LeafInj0VPf LateralTheory.E.LeafSHPtPf LateralTheory.E.StrictHenselianNeighbourhood

namespace LateralTheory.E.EtaleNeighbourhoodSystem

section
variable {S : Scheme.{0}} {Ω : Type} [Field Ω] [IsSepClosed Ω] (s : Spec (CommRingCat.of Ω) ⟶ S)

abbrev Fb : S.Etale ⥤ Type := Scheme.Etale.forget S ⋙ coyoneda.obj (op (Over.mk s))

/- English proof (translation)
Break down `i with ⟨X, x⟩` into its components or cases. Consider the cases of `X with | _ Y f`. Take `⟨y, hy, rfl⟩` from `Over.homMk_surjective x`. Simplify using `at y hy`. Choose the witnesses or unpack the hypotheses as in `⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec R ⟶ Y) (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by`.

Take `⟨R, j, _, hj, _⟩` from `Scheme.exists_affine_mem_range_and_range_subset (x := y.base default) (U := ⊤) (by simp)`. Use `⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[Subsingleton.elim a default]` and apply the resulting hypothesis. Use `⟨⟨(Scheme.AffineEtale.Spec S).obj (Scheme.AffineEtale.mk (j ≫ f)), Over.homMk y'⟩, ?_, ⟨⟨MorphismProperty.Over.homMk j rfl trivial, by cat_disch⟩⟩⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `IsAffine (Spec R)`. Use `infer_instance`.
-/
lemma exists_affine (i : (Fb s).Elements) :
    ∃ j : (Fb s).Elements, IsAffine j.1.left ∧ Nonempty (j ⟶ i) := by
  rcases i with ⟨X, x⟩
  cases X with | _ Y f
  obtain ⟨y, hy, rfl⟩ := Over.homMk_surjective x
  dsimp at y hy
  obtain ⟨R, j, _, y', rfl⟩ : ∃ (R : CommRingCat) (j : Spec R ⟶ Y)
      (_ : IsOpenImmersion j) (y' : _ ⟶ _), y' ≫ j = y := by
    obtain ⟨R, j, _, hj, _⟩ := Scheme.exists_affine_mem_range_and_range_subset
      (x := y.base default) (U := ⊤) (by simp)
    refine ⟨R, j, inferInstance, _, IsOpenImmersion.lift_fac j y ?_⟩
    rintro _ ⟨a, rfl⟩
    rwa [Subsingleton.elim a default]
  refine ⟨⟨(Scheme.AffineEtale.Spec S).obj (Scheme.AffineEtale.mk (j ≫ f)), Over.homMk y'⟩, ?_,
    ⟨⟨MorphismProperty.Over.homMk j rfl trivial, by cat_disch⟩⟩⟩
  change IsAffine (Spec R)
  infer_instance

/- English proof (translation)
Use `haveI : InitiallySmall.{0} (Fb s).Elements := (Scheme.pointSmallEtale s).initiallySmall`. Take `⟨Q0, hQ0, h0⟩` from `InitiallySmall.exists_small_weakly_initial_set.{0} (Fb s).Elements`. Use `choose g hg hg' using exists_affine s`. Use `⟨g '' Q0, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `haveI := hQ0`.

Use `infer_instance`. Introduce and unpack `_ ⟨i, -, rfl⟩`. Conclude with `hg i`. Introduce `i`. Take `⟨k, hk, ⟨f⟩⟩` from `h0 i`.

Conclude with `⟨g k, ⟨k, hk, rfl⟩, ⟨(hg' k).some ≫ f⟩⟩`.
-/
lemma exists_small : ∃ (Q : Set (Fb s).Elements), Small.{0} Q ∧ (∀ j ∈ Q, IsAffine j.1.left) ∧
    ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i) := by
  haveI : InitiallySmall.{0} (Fb s).Elements := (Scheme.pointSmallEtale s).initiallySmall
  obtain ⟨Q0, hQ0, h0⟩ := InitiallySmall.exists_small_weakly_initial_set.{0} (Fb s).Elements
  choose g hg hg' using exists_affine s
  refine ⟨g '' Q0, ?_, ?_, ?_⟩
  · haveI := hQ0; infer_instance
  · rintro _ ⟨i, -, rfl⟩; exact hg i
  · intro i
    obtain ⟨k, hk, ⟨f⟩⟩ := h0 i
    exact ⟨g k, ⟨k, hk, rfl⟩, ⟨(hg' k).some ≫ f⟩⟩

variable (Q : Set (Fb s).Elements) [Small.{0} Q]

def ι : Shrink.{0} Q → (Fb s).Elements := fun q => ((equivShrink Q).symm q).1
/- English proof (translation)
The claim follows from `((equivShrink Q).symm q).2`.
-/
lemma ι_mem (q : Shrink.{0} Q) : ι s Q q ∈ Q := ((equivShrink Q).symm q).2

abbrev Jc := InducedCategory (Fb s).Elements (ι s Q)

/- English proof (translation)
Take `⟨j, hj, ⟨f⟩⟩` from `hwi d`. Conclude with `⟨equivShrink Q ⟨j, hj⟩, ⟨eqToHom (by simp [ι]) ≫ f⟩⟩`.
-/
lemma exists_of_wi (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) (d : (Fb s).Elements) :
    ∃ c : Jc s Q, Nonempty ((ι s Q c) ⟶ d) := by
  obtain ⟨j, hj, ⟨f⟩⟩ := hwi d
  exact ⟨equivShrink Q ⟨j, hj⟩, ⟨eqToHom (by simp [ι]) ≫ f⟩⟩

/- English proof (translation)
Establish `h` using `exists_of_wi s Q hwi`. Take `⟨d⟩` from `IsCofiltered.nonempty (C := (Fb s).Elements)`. Use `exact`. Use the proof step `{ cone_objs := fun a b => by`. Take `⟨c, ⟨hc⟩⟩` from `h (IsCofiltered.min (ι s Q a) (ι s Q b))`.

Conclude with `⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.minToLeft _ _), InducedCategory.homMk (hc ≫ IsCofiltered.minToRight _ _), trivial⟩`. Use `cone_maps := fun a b f g => by`. Take `⟨c, ⟨hc⟩⟩` from `h (IsCofiltered.eq f.hom g.hom)`. Use `⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.eqHom f.hom g.hom), ?_⟩` and prove the remaining obligations. Apply `InducedCategory.hom_ext` to reduce the goal to its premises.

Use `show (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ f.hom = (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ g.hom`. Rewrite using `[Category.assoc, Category.assoc, IsCofiltered.eq_condition]`. Use `nonempty := ⟨(h d).choose⟩ }`.
-/
lemma cof (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) : IsCofiltered (Jc s Q) := by
  have h := exists_of_wi s Q hwi
  obtain ⟨d⟩ := IsCofiltered.nonempty (C := (Fb s).Elements)
  exact
  { cone_objs := fun a b => by
      obtain ⟨c, ⟨hc⟩⟩ := h (IsCofiltered.min (ι s Q a) (ι s Q b))
      exact ⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.minToLeft _ _),
        InducedCategory.homMk (hc ≫ IsCofiltered.minToRight _ _), trivial⟩
    cone_maps := fun a b f g => by
      obtain ⟨c, ⟨hc⟩⟩ := h (IsCofiltered.eq f.hom g.hom)
      refine ⟨c, InducedCategory.homMk (hc ≫ IsCofiltered.eqHom f.hom g.hom), ?_⟩
      apply InducedCategory.hom_ext
      show (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ f.hom = (hc ≫ IsCofiltered.eqHom f.hom g.hom) ≫ g.hom
      rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
    nonempty := ⟨(h d).choose⟩ }

def G : Jc s Q ⥤ Scheme.{0} :=
  inducedFunctor (ι s Q) ⋙ CategoryOfElements.π (Fb s) ⋙ Scheme.Etale.forget S ⋙ Over.forget S

def D : (Jc s Q)ᵒᵖ ⥤ CommRingCat.{0} := (G s Q).op ⋙ Scheme.Γ

end

section Sys
variable {B : Scheme.{0}} {U : B.Etale} {Ω : Type} [Field Ω] [IsSepClosed Ω]
  (s : Spec (CommRingCat.of Ω) ⟶ U.left) (Q : Set (Fb s).Elements) [Small.{0} Q]

def pt (j : Jc s Q) : Spec (CommRingCat.of Ω) ⟶ (G s Q).obj j := (ι s Q j).2.left

/- English proof (translation)
The claim follows from `Over.w (ι s Q j).2`.
-/
lemma pt_w (j : Jc s Q) : pt s Q j ≫ (ι s Q j).1.hom = s := Over.w (ι s Q j).2

/- English proof (translation)
The claim follows from `MorphismProperty.Over.w m.hom.1`.
-/
lemma G_w {j k : Jc s Q} (m : k ⟶ j) : (G s Q).map m ≫ (ι s Q j).1.hom = (ι s Q k).1.hom :=
  MorphismProperty.Over.w m.hom.1

/- English proof (translation)
The claim follows from `congrArg CommaMorphism.left m.hom.2`.
-/
lemma pt_map {j k : Jc s Q} (m : k ⟶ j) : pt s Q k ≫ (G s Q).map m = pt s Q j :=
  congrArg CommaMorphism.left m.hom.2

def V (j : (Jc s Q)ᵒᵖ) : B.Etale :=
  MorphismProperty.Over.mk ⊤ ((ι s Q j.unop).1.hom ≫ U.hom)
    (by have := (ι s Q j.unop).1.prop; have := U.prop; exact Etale.etale_comp _ _)

def a (j : (Jc s Q)ᵒᵖ) : V s Q j ⟶ U :=
  MorphismProperty.Over.homMk (ι s Q j.unop).1.hom rfl trivial

variable (haff : ∀ j ∈ Q, IsAffine j.1.left)
include haff

/- English proof (translation)
The claim follows from `haff _ (ι_mem s Q j)`.
-/
lemma aff (j : Jc s Q) : IsAffine ((G s Q).obj j) := haff _ (ι_mem s Q j)

def e (j : (Jc s Q)ᵒᵖ) : Sp ((D s Q).obj j) ⟶ (G s Q).obj j.unop :=
  haveI := aff s Q haff j.unop; ((G s Q).obj j.unop).isoSpec.inv

/- English proof (translation)
Unfold `e`. Conclude with `Iso.isIso_inv _`.
-/
lemma e_iso (j : (Jc s Q)ᵒᵖ) : IsIso (e s Q haff j) := by unfold e; exact Iso.isIso_inv _

def l (j : (Jc s Q)ᵒᵖ) : Spec (CommRingCat.of Ω) ⟶ Sp ((D s Q).obj j) :=
  haveI := aff s Q haff j.unop; pt s Q j.unop ≫ ((G s Q).obj j.unop).isoSpec.hom

/- English proof (translation)
Unfold `l e`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))`.
-/
lemma l_e (j : (Jc s Q)ᵒᵖ) : l s Q haff j ≫ e s Q haff j = pt s Q j.unop := by
  unfold l e
  exact (Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) (Iso.hom_inv_id _)).trans (Category.comp_id _))

/- English proof (translation)
Use `haveI := aff s Q haff j.unop`. Use `haveI := aff s Q haff k.unop`. Conclude with `Scheme.isoSpec_inv_naturality ((G s Q).map f.unop)`.
-/
lemma nat {j k : (Jc s Q)ᵒᵖ} (f : j ⟶ k) :
    Spec.map ((D s Q).map f) ≫ e s Q haff j = e s Q haff k ≫ (G s Q).map f.unop := by
  haveI := aff s Q haff j.unop; haveI := aff s Q haff k.unop
  exact Scheme.isoSpec_inv_naturality ((G s Q).map f.unop)

def t (j0 : (Jc s Q)ᵒᵖ) : Sp (colimit.cocone (D s Q)).pt ⟶ U.left :=
  Spec.map ((colimit.cocone (D s Q)).ι.app j0) ≫ e s Q haff j0 ≫ (ι s Q j0.unop).1.hom

/- English proof (translation)
Use `haveI := cof s Q hwi`. Take `⟨j0⟩` from `IsFiltered.nonempty (C := (Jc s Q)ᵒᵖ)`. Establish `hcomp0 : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k), Spec.map ((D s Q).map f) ≫ e s Q haff j ≫ (a s Q j).left = e s Q haff k ≫ (a s Q k).left`. Introduce `j k f`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (a s Q j).left) (nat s Q haff f)).trans ((Category.assoc _ _ _).trans (congrArg (e s Q haff k ≫ ·) (G_w s Q f.unop))))`.

Establish `key : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k), Spec.map ((colimit.cocone (D s Q)).ι.app j) ≫ e s Q haff j ≫ (a s Q j).left = Spec.map ((colimit.cocone (D s Q)).ι.app k) ≫ e s Q haff k ≫ (a s Q k).left`. Introduce `j k f`. Rewrite using `[← (colimit.cocone (D s Q)).w f, Spec.map_comp, Category.assoc, hcomp0 j k f]`. Use `⟨(Jc s Q)ᵒᵖ, inferInstance, inferInstance, D s Q, colimit.cocone _, colimit.isColimit _, V s Q, a s Q, l s Q haff, e s Q haff, t s Q haff j0, hx, e_iso s Q haff, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `j erw [reassoc_of% (l_e s Q haff j)]`.

Conclude with `pt_w s Q j.unop`. Introduce `j k f`. Use `hcomp0 j k f` as an intermediate fact. Simplify using `only [CommRingCat.ofHom_hom]`. Conclude with `this`.

Introduce `j`. Simplify using `only [CommRingCat.ofHom_hom]`. Take `⟨k, f, g, -⟩` from `IsFilteredOrEmpty.cocone_objs j j0`. Use `erw [key j k f, ← key j0 k g]`. Both sides reduce to the same expression.

Introduce `j k f haveI := e_iso s Q haff j`. Rewrite using `[← cancel_mono (e s Q haff j)]`. Simplify using `only [CommRingCat.ofHom_hom, Category.assoc]`. Rewrite using `[nat, reassoc_of% (l_e s Q haff k), l_e, pt_map]`. Introduce `U' b l' hl'`.

Set `X' : U.left.Etale` to `MorphismProperty.Over.mk ⊤ b.left inferInstance`. Take `⟨c, ⟨hc⟩⟩` from `exists_of_wi s Q hwi ⟨X', Over.homMk l' hl'⟩`. Use `⟨op c, hc.1.left, MorphismProperty.Over.w hc.1, ?_⟩` and prove the remaining obligations. Use `erw [reassoc_of% (l_e s Q haff (op c))]`. Conclude with `congrArg CommaMorphism.left hc.2`.

Introduce `U' b j g g' hg hg' heq erw [reassoc_of% (l_e s Q haff j), reassoc_of% (l_e s Q haff j)] at heq`. Set `X' : U.left.Etale` to `MorphismProperty.Over.mk ⊤ b.left inferInstance`. Establish `hy : (pt s Q j.unop ≫ g) ≫ b.left = s`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) hg).trans (pt_w s Q j.unop))`. Set `y : (Fb s).Elements` to `⟨X', Over.homMk (pt s Q j.unop ≫ g) hy⟩`.

Set `u : ι s Q j.unop ⟶ y` to `⟨MorphismProperty.Over.homMk (B := X') g hg trivial, by apply Over.OverMorphism.ext; rfl⟩`. Set `u' : ι s Q j.unop ⟶ y` to `⟨MorphismProperty.Over.homMk (B := X') g' hg' trivial, by apply Over.OverMorphism.ext; exact heq.symm⟩`. Take `⟨c, ⟨hc⟩⟩` from `exists_of_wi s Q hwi (IsCofiltered.eq u u')`. Set `m : c ⟶ j.unop` to `InducedCategory.homMk (hc ≫ IsCofiltered.eqHom u u')`. Use `⟨op c, m.op, ?_⟩` and prove the remaining obligations.

Establish `h0 : (hc ≫ IsCofiltered.eqHom u u') ≫ u = (hc ≫ IsCofiltered.eqHom u u') ≫ u'`. Rewrite using `[Category.assoc, Category.assoc, IsCofiltered.eq_condition]`. Establish `h1` using `congrArg (fun z => z.1.left) h0`. Simplify using `only [CommRingCat.ofHom_hom]`. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) (nat s Q haff m.op)).trans ((Category.assoc _ _ _).trans ((congrArg (e s Q haff (op c) ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g') (nat s Q haff m.op)).symm.trans (Category.assoc _ _ _))))))`.
-/
lemma main (x : U.left) (hx : s default = x) (hwi : ∀ i, ∃ j ∈ Q, Nonempty (j ⟶ i)) :
    ∃ (J : Type) (_ : SmallCategory J) (_ : IsFiltered J) (D : J ⥤ CommRingCat.{0}) (c : Cocone D)
    (_ : IsColimit c) (V : J → B.Etale) (a : ∀ j, V j ⟶ U) (l : ∀ j, Spec (CommRingCat.of Ω) ⟶ Sp (D.obj j))
    (e : ∀ j, Sp (D.obj j) ⟶ (V j).left) (t : Sp c.pt ⟶ U.left), IsPtNb U x Ω s D c V a l e t := by
  haveI := cof s Q hwi
  obtain ⟨j0⟩ := IsFiltered.nonempty (C := (Jc s Q)ᵒᵖ)
  have hcomp0 : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k),
      Spec.map ((D s Q).map f) ≫ e s Q haff j ≫ (a s Q j).left = e s Q haff k ≫ (a s Q k).left := by
    intro j k f
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (a s Q j).left) (nat s Q haff f)).trans
      ((Category.assoc _ _ _).trans (congrArg (e s Q haff k ≫ ·) (G_w s Q f.unop))))
  have key : ∀ (j k : (Jc s Q)ᵒᵖ) (f : j ⟶ k),
      Spec.map ((colimit.cocone (D s Q)).ι.app j) ≫ e s Q haff j ≫ (a s Q j).left =
        Spec.map ((colimit.cocone (D s Q)).ι.app k) ≫ e s Q haff k ≫ (a s Q k).left := by
    intro j k f
    rw [← (colimit.cocone (D s Q)).w f, Spec.map_comp, Category.assoc, hcomp0 j k f]
  refine ⟨(Jc s Q)ᵒᵖ, inferInstance, inferInstance, D s Q, colimit.cocone _, colimit.isColimit _,
    V s Q, a s Q, l s Q haff, e s Q haff, t s Q haff j0, hx, e_iso s Q haff, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j
    erw [reassoc_of% (l_e s Q haff j)]
    exact pt_w s Q j.unop
  · intro j k f
    have := hcomp0 j k f
    simp only [CommRingCat.ofHom_hom]
    exact this
  · intro j
    simp only [CommRingCat.ofHom_hom]
    obtain ⟨k, f, g, -⟩ := IsFilteredOrEmpty.cocone_objs j j0
    erw [key j k f, ← key j0 k g]
    rfl
  · intro j k f
    haveI := e_iso s Q haff j
    rw [← cancel_mono (e s Q haff j)]
    simp only [CommRingCat.ofHom_hom, Category.assoc]
    rw [nat, reassoc_of% (l_e s Q haff k), l_e, pt_map]
  · intro U' b l' hl'
    let X' : U.left.Etale := MorphismProperty.Over.mk ⊤ b.left inferInstance
    obtain ⟨c, ⟨hc⟩⟩ := exists_of_wi s Q hwi ⟨X', Over.homMk l' hl'⟩
    refine ⟨op c, hc.1.left, MorphismProperty.Over.w hc.1, ?_⟩
    erw [reassoc_of% (l_e s Q haff (op c))]
    exact congrArg CommaMorphism.left hc.2
  · intro U' b j g g' hg hg' heq
    erw [reassoc_of% (l_e s Q haff j), reassoc_of% (l_e s Q haff j)] at heq
    let X' : U.left.Etale := MorphismProperty.Over.mk ⊤ b.left inferInstance
    have hy : (pt s Q j.unop ≫ g) ≫ b.left = s := by
      exact (Category.assoc _ _ _).trans ((congrArg (pt s Q j.unop ≫ ·) hg).trans (pt_w s Q j.unop))
    let y : (Fb s).Elements := ⟨X', Over.homMk (pt s Q j.unop ≫ g) hy⟩
    let u : ι s Q j.unop ⟶ y := ⟨MorphismProperty.Over.homMk (B := X') g hg trivial,
      by apply Over.OverMorphism.ext; rfl⟩
    let u' : ι s Q j.unop ⟶ y := ⟨MorphismProperty.Over.homMk (B := X') g' hg' trivial,
      by apply Over.OverMorphism.ext; exact heq.symm⟩
    obtain ⟨c, ⟨hc⟩⟩ := exists_of_wi s Q hwi (IsCofiltered.eq u u')
    let m : c ⟶ j.unop := InducedCategory.homMk (hc ≫ IsCofiltered.eqHom u u')
    refine ⟨op c, m.op, ?_⟩
    have h0 : (hc ≫ IsCofiltered.eqHom u u') ≫ u = (hc ≫ IsCofiltered.eqHom u u') ≫ u' := by
      rw [Category.assoc, Category.assoc, IsCofiltered.eq_condition]
    have h1 := congrArg (fun z => z.1.left) h0
    simp only [CommRingCat.ofHom_hom]
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g) (nat s Q haff m.op)).trans ((Category.assoc _ _ _).trans
      ((congrArg (e s Q haff (op c) ≫ ·) h1).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ g') (nat s Q haff m.op)).symm.trans (Category.assoc _ _ _))))))

end Sys

/- English proof (translation)
Introduce `B U x`. Set `Ω` to `SeparableClosure (U.left.residueField x)`. Set `s : Spec (CommRingCat.of Ω) ⟶ U.left` to `Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫ U.left.fromSpecResidueField x`. Apply the tactic sequence `have hx : s default = x := by first | exact Scheme.fromSpecResidueField_apply x _ | (simp [s]; exact Scheme.fromSpecResidueField_apply x _)`. Take `⟨Q, hQs, haff, hwi⟩` from `exists_small s`.

Use `haveI := hQs`. Conclude with `⟨Ω, inferInstance, inferInstance, s, main s Q haff x hx hwi⟩`.
-/
theorem LeafSHNbSys_of : LeafSHNbSys := by
  intro B U x
  let Ω := SeparableClosure (U.left.residueField x)
  let s : Spec (CommRingCat.of Ω) ⟶ U.left :=
    Spec.map (CommRingCat.ofHom (algebraMap (U.left.residueField x) Ω)) ≫ U.left.fromSpecResidueField x
  have hx : s default = x := by
    first | exact Scheme.fromSpecResidueField_apply x _ | (simp [s]; exact Scheme.fromSpecResidueField_apply x _)
  obtain ⟨Q, hQs, haff, hwi⟩ := exists_small s
  haveI := hQs
  exact ⟨Ω, inferInstance, inferInstance, s, main s Q haff x hx hwi⟩

end LateralTheory.E.EtaleNeighbourhoodSystem
