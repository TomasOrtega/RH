import Development.EtaleCohomology.EtaleSheaves.ContPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ContPf

namespace LateralTheory.E.ContAffPf

/- English proof (translation)
Rewrite using `[Iso.comp_inv_eq, Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]`.
-/
lemma isoSpec_inv_nat {X Y : Scheme.{0}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y) :
    Spec.map f.appTop ≫ Y.isoSpec.inv = X.isoSpec.inv ≫ f := by
  rw [Iso.comp_inv_eq, Category.assoc, ← Scheme.isoSpec_hom_naturality, Iso.inv_hom_id_assoc]

/- English proof (translation)
Rewrite using `[← pull_comp, h, pull_comp]`.
-/
lemma pp {R : Type} [CommRing R] {A B C E : Spc} (a : A ⟶ B) (b : B ⟶ E) (c : A ⟶ C) (d : C ⟶ E) (h : a ≫ b = c ≫ d)
    (F : Shv R) (n : ℤ) (x : H R E F n) : pull R a F n (pull R b F n x) = pull R c F n (pull R d F n x) := by
  rw [← pull_comp, h, pull_comp]

/- English proof (translation)
Take `⟨hE⟩` from `nonempty_isColimit_Γ_mapCocone D c hc`. Establish `hP' : ∀ j, IsAffine (((Functor.const I).obj c.pt).obj j)` using `fun _ => hP`. Establish `B` using `hB1 q (D.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c.op) hE n i`. Take `⟨j0⟩` from `IsCofiltered.nonempty (C := I)`. Establish `huP : IsUnit (q : Γ(c.pt, ⊤))`.

Use `(hu j0).map (c.π.app j0).appTop.hom` as an intermediate fact. Simplify using `using this`. Prove the components needed by the constructor for the conclusion. Introduce `x`. Take `⟨j, y, hy⟩` from `B.1 (pull _ (sch.map c.pt.isoSpec.inv) _ _ x) huP`.

Use `⟨j.unop, pull _ (sch.map (D.obj j.unop).isoSpec.hom) _ _ y, ?_⟩` and prove the remaining obligations. Establish `key` using `pp (R := ZMod q) (sch.map (c.π.app j.unop)) (sch.map (D.obj j.unop).isoSpec.hom) (sch.map c.pt.isoSpec.hom) (sch.map (Spec.map (c.π.app j.unop).appTop)) (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_natur …`. Use `key.trans ?_` and prove the remaining obligations. Establish `hy' : pull (ZMod q) (sch.map (Spec.map (c.π.app j.unop).appTop)) (tw q i) n y = pull (ZMod q) (sch.map c.pt.isoSpec.inv) (tw q i) n x` using `hy`. Rewrite using `[hy', ← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id]`.

Use `erw [CategoryTheory.Functor.map_id, pull_id]`. Introduce `j y hy`. Take `⟨k, f, hk⟩` from `B.2 (Opposite.op j) (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) (hu j) (by`. Establish `key2` using `pp (R := ZMod q) (sch.map (Spec.map (c.π.app j).appTop)) (sch.map (D.obj j).isoSpec.inv) (sch.map c.pt.isoSpec.inv) (sch.map (c.π.app j)) (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (isoSpec_inv_nat _)) (tw q i) n y`. Conclude with `key2.trans (by rw [hy]; exact map_zero _))`.

Use `⟨k.unop, f.unop, ?_⟩` and prove the remaining obligations. Establish `e1 : y = pull _ (sch.map (D.obj j).isoSpec.hom) _ _ (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y)`. Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]`. Rewrite using `[e1]`. Establish `key3` using `pp (R := ZMod q) (sch.map (D.map f.unop)) (sch.map (D.obj j).isoSpec.hom) (sch.map (D.obj k.unop).isoSpec.hom) (sch.map (Spec.map (D.map f.unop).appTop)) (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_natu …`.

Use `key3.trans ?_` and prove the remaining obligations. Establish `hk' : pull (ZMod q) (sch.map (Spec.map (D.map f.unop).appTop)) (tw q i) n (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) = 0` using `hk`. Rewrite using `[hk', map_zero]`.
-/
theorem aff_case (hB1 : B1) (q : ℕ) {I : Type} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{0}) (c : Cone D)
    (hc : IsLimit c) (ha : ∀ {j k : I} (f : j ⟶ k), IsAffineHom (D.map f)) (hcs : ∀ j, CompactSpace (D.obj j))
    (hqs : ∀ j, QuasiSeparatedSpace (D.obj j)) (hu : ∀ j, IsUnit (q : Γ(D.obj j, ⊤)))
    (hA : ∀ j, IsAffine (D.obj j)) (hP : IsAffine c.pt) (n i : ℤ) :
    (∀ x : Ht q (sch.obj c.pt) n i, ∃ j y, pull _ (sch.map (c.π.app j)) _ _ y = x) ∧
    ∀ j (y : Ht q (sch.obj (D.obj j)) n i), pull _ (sch.map (c.π.app j)) _ _ y = 0 →
      ∃ (k : I) (f : k ⟶ j), pull _ (sch.map (D.map f)) _ _ y = 0 := by
  obtain ⟨hE⟩ := nonempty_isColimit_Γ_mapCocone D c hc
  have hP' : ∀ j, IsAffine (((Functor.const I).obj c.pt).obj j) := fun _ => hP
  have B := hB1 q (D.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c.op) hE n i
  obtain ⟨j0⟩ := IsCofiltered.nonempty (C := I)
  have huP : IsUnit (q : Γ(c.pt, ⊤)) := by
    have := (hu j0).map (c.π.app j0).appTop.hom
    simpa using this
  constructor
  · intro x
    obtain ⟨j, y, hy⟩ := B.1 (pull _ (sch.map c.pt.isoSpec.inv) _ _ x) huP
    refine ⟨j.unop, pull _ (sch.map (D.obj j.unop).isoSpec.hom) _ _ y, ?_⟩
    have key := pp (R := ZMod q) (sch.map (c.π.app j.unop)) (sch.map (D.obj j.unop).isoSpec.hom)
      (sch.map c.pt.isoSpec.hom) (sch.map (Spec.map (c.π.app j.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n y
    refine key.trans ?_
    have hy' : pull (ZMod q) (sch.map (Spec.map (c.π.app j.unop).appTop)) (tw q i) n y =
      pull (ZMod q) (sch.map c.pt.isoSpec.inv) (tw q i) n x := hy
    rw [hy', ← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id]
    erw [CategoryTheory.Functor.map_id, pull_id]
  · intro j y hy
    obtain ⟨k, f, hk⟩ := B.2 (Opposite.op j) (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) (hu j) (by
      have key2 := pp (R := ZMod q) (sch.map (Spec.map (c.π.app j).appTop)) (sch.map (D.obj j).isoSpec.inv)
        (sch.map c.pt.isoSpec.inv) (sch.map (c.π.app j))
        (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (isoSpec_inv_nat _)) (tw q i) n y
      exact key2.trans (by rw [hy]; exact map_zero _))
    refine ⟨k.unop, f.unop, ?_⟩
    have e1 : y = pull _ (sch.map (D.obj j).isoSpec.hom) _ _ (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) := by
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
    rw [e1]
    have key3 := pp (R := ZMod q) (sch.map (D.map f.unop)) (sch.map (D.obj j).isoSpec.hom)
      (sch.map (D.obj k.unop).isoSpec.hom) (sch.map (Spec.map (D.map f.unop).appTop))
      (by rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]; exact congrArg sch.map (Scheme.isoSpec_hom_naturality _).symm) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y)
    refine key3.trans ?_
    have hk' : pull (ZMod q) (sch.map (Spec.map (D.map f.unop).appTop)) (tw q i) n
      (pull _ (sch.map (D.obj j).isoSpec.inv) _ _ y) = 0 := hk
    rw [hk', map_zero]

/- English proof (translation)
Introduce `h X _ q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i`. Establish `: IsAffine (D.obj j0)` using `IsAffine.of_isIso e.hom`. Establish `hc' : IsLimit (c.whisker (Over.forget j0))` using `(Functor.Initial.isLimitWhiskerEquiv (Over.forget j0) c).symm hc`. Establish `hA : ∀ k : Over j0, IsAffine ((Over.forget j0 ⋙ D).obj k)` using `fun k => by`. Establish `i1` using `ha k.hom`.

Establish `i2 : IsAffine (D.obj ((Functor.fromPUnit j0).obj k.right))` using `‹IsAffine (D.obj j0)›`. Conclude with `@isAffine_of_isAffineHom _ _ (D.map k.hom) (ha k.hom) i2`. Establish `hP : IsAffine c.pt`. Establish `: ∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f)` using `ha`. Use `hcs` as an intermediate fact.

Use `hqs` as an intermediate fact. Use `isAffineHom_π_app D c hc j0` as an intermediate fact. Conclude with `isAffine_of_isAffineHom (c.π.app j0)`. Establish `R` using `aff_case h.b1 q (Over.forget j0 ⋙ D) (c.whisker (Over.forget j0)) hc' (fun f => ha _) (fun k => hcs _) (fun k => hqs _) (fun k => hu _) hA hP n i`. Use `⟨fun x => ?_, fun j y hy => ?_⟩` and prove the remaining obligations.

Take `⟨k, y, hy⟩` from `R.1 x`. Conclude with `⟨k.left, y, hy⟩`. Take `⟨k, g, h0, -⟩` from `IsCofilteredOrEmpty.cone_objs j j0`. Take `⟨l, f, hf⟩` from `R.2 (Over.mk h0) (pull _ (sch.map (D.map g)) _ _ y) (by show pull _ (sch.map (c.π.app k)) _ _ _ = 0`. Rewrite using `[← pull_comp, ← CategoryTheory.Functor.map_comp, c.w]`.

Conclude with `hy)`. Use `⟨l.left, f.left ≫ g, ?_⟩` and prove the remaining obligations. Rewrite using `[D.map_comp, CategoryTheory.Functor.map_comp, pull_comp]`. Conclude with `hf`.
-/
theorem ContAff_of : ContAff := by
  intro h X _ q J _ _ D c hc ha hcs hqs hu j0 ⟨e⟩ n i
  have : IsAffine (D.obj j0) := IsAffine.of_isIso e.hom
  have hc' : IsLimit (c.whisker (Over.forget j0)) := (Functor.Initial.isLimitWhiskerEquiv (Over.forget j0) c).symm hc
  have hA : ∀ k : Over j0, IsAffine ((Over.forget j0 ⋙ D).obj k) := fun k => by
    have i1 := ha k.hom
    have i2 : IsAffine (D.obj ((Functor.fromPUnit j0).obj k.right)) := ‹IsAffine (D.obj j0)›
    exact @isAffine_of_isAffineHom _ _ (D.map k.hom) (ha k.hom) i2
  have hP : IsAffine c.pt := by
    have : ∀ {j k : J} (f : j ⟶ k), IsAffineHom (D.map f) := ha
    have := hcs; have := hqs
    have := isAffineHom_π_app D c hc j0
    exact isAffine_of_isAffineHom (c.π.app j0)
  have R := aff_case h.b1 q (Over.forget j0 ⋙ D) (c.whisker (Over.forget j0)) hc' (fun f => ha _)
    (fun k => hcs _) (fun k => hqs _) (fun k => hu _) hA hP n i
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨k, y, hy⟩ := R.1 x
    exact ⟨k.left, y, hy⟩
  · obtain ⟨k, g, h0, -⟩ := IsCofilteredOrEmpty.cone_objs j j0
    obtain ⟨l, f, hf⟩ := R.2 (Over.mk h0) (pull _ (sch.map (D.map g)) _ _ y) (by
      show pull _ (sch.map (c.π.app k)) _ _ _ = 0
      rw [← pull_comp, ← CategoryTheory.Functor.map_comp, c.w]
      exact hy)
    refine ⟨l.left, f.left ≫ g, ?_⟩
    rw [D.map_comp, CategoryTheory.Functor.map_comp, pull_comp]
    exact hf

end LateralTheory.E.ContAffPf
