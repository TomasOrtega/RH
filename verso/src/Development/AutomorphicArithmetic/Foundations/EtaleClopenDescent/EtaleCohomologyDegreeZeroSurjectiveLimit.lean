import Mathlib
import Development.EtaleCohomology.EtaleSheaves.CovOfPoints
import Development.EtaleCohomology.EtaleSheaves.RelativeCohomologyForgetInjectiveDegreeZeroOfSub
import Development.EtaleCohomology.EtaleSheaves.SecondDegreeKilling.LeafKill2Of
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCofilteredLimitAffineEtaleOfIsStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStrictlyHenselianEtaleStalkOverPointStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafSectionsSepGlueOfSurjectiveFamily
import Development.EtaleCohomology.EtaleDuality.TASCohSplitPfEmpty

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace UpperTheory.Cb.TensorPullbackSquares
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

private abbrev TF {S X : Scheme.{0}} (r : X ⟶ S) : Over S ⥤ Scheme.{0} := Over.pullback r ⋙ Over.forget X

private def tm {S X : Scheme.{0}} (r : X ⟶ S) {Z Z' : Over S} (g : Z ⟶ Z') :
    pullback Z.hom r ⟶ pullback Z'.hom r := (TF r).map g

/- English proof (translation)
Simplify using `only [tm, TF, Functor.comp_map, Over.forget_map]`. Conclude with `pullback.lift_fst _ _ _`.
-/
private theorem tm_fst {S X : Scheme.{0}} (r : X ⟶ S) {Z Z' : Over S} (g : Z ⟶ Z') :
    tm r g ≫ pullback.fst Z'.hom r = pullback.fst Z.hom r ≫ g.left := by
  simp only [tm, TF, Functor.comp_map, Over.forget_map]
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Simplify using `only [tm, TF, Functor.comp_map, Over.forget_map]`. Conclude with `pullback.lift_snd _ _ _`.
-/
private theorem tm_snd {S X : Scheme.{0}} (r : X ⟶ S) {Z Z' : Over S} (g : Z ⟶ Z') :
    tm r g ≫ pullback.snd Z'.hom r = pullback.snd Z.hom r := by
  simp only [tm, TF, Functor.comp_map, Over.forget_map]
  exact pullback.lift_snd _ _ _

/- English proof (translation)
Use `IsPullback.of_right (h₁₂ := pullback.snd Z'.hom r) (v₁₃ := r) (h₂₂ := Z'.hom) ?_ (tm_fst r g) ?_` and prove the remaining obligations. Rewrite using `[tm_snd, Over.w g]`. Conclude with `(IsPullback.of_hasPullback Z.hom r).flip`. Conclude with `(IsPullback.of_hasPullback Z'.hom r).flip`.
-/
private theorem tm_isPullback {S X : Scheme.{0}} (r : X ⟶ S) {Z Z' : Over S} (g : Z ⟶ Z') :
    IsPullback (tm r g) (pullback.fst Z.hom r) (pullback.fst Z'.hom r) g.left := by
  refine IsPullback.of_right (h₁₂ := pullback.snd Z'.hom r) (v₁₃ := r) (h₂₂ := Z'.hom) ?_ (tm_fst r g) ?_
  · rw [tm_snd, Over.w g]
    exact (IsPullback.of_hasPullback Z.hom r).flip
  · exact (IsPullback.of_hasPullback Z'.hom r).flip

/- English proof (translation)
Rewrite using `[Functor.map_comp, pull_comp]`.
-/
private theorem pp (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X)
    (x : H R (sch.obj X) F n) :
    pull R (sch.map g) F n (pull R (sch.map f) F n x) = pull R (sch.map (g ≫ f)) F n x := by
  rw [Functor.map_comp, pull_comp]

/- English proof (translation)
Establish `h` using `hq.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom`. Simplify using `using h`.
-/
private theorem unit_of {k : Type} [Field k] {q : ℕ} (hq : IsUnit (q : k)) {Z : Scheme.{0}} (g : Z ⟶ Sp k) :
    IsUnit (q : Γ(Z, ⊤)) := by
  have h := hq.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appTop).hom
  simpa using h

/- English proof (translation)
Rewrite using `[pp, pp, Scheme.isoSpec_hom_naturality]`.
-/
private theorem pull_comp_isoSpec_naturality (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {X Y : Scheme.{0}} [IsAffine X]
    [IsAffine Y] (f : X ⟶ Y) (z : H R (sch.obj (Spec Γ(Y, ⊤))) F n) :
    pull R (sch.map f) F n (pull R (sch.map Y.isoSpec.hom) F n z) =
      pull R (sch.map X.isoSpec.hom) F n (pull R (sch.map (Spec.map f.appTop)) F n z) := by
  rw [pp, pp, Scheme.isoSpec_hom_naturality]

/- English proof (translation)
Rewrite using `[pp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]`.
-/
private theorem pull_hom_pull_inv_eq_self (R : Type) [CommRing R] (F : Shv R) (n : ℤ) {X Y : Scheme.{0}} (e : X ≅ Y)
    (x : H R (sch.obj X) F n) : pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n x) = x := by
  rw [pp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]

/- English proof (translation)
Establish `hGo : ∀ j, IsAffine (G.op.obj j).unop` using `fun j => hG j.unop`. Establish `hGi : ∀ j, IsAffine (G.obj j)` using `hG`. Establish `hpt : IsAffine c.pt` using `Scheme.isAffine_of_isLimit c hc`. Establish `hcol : IsColimit (Scheme.Γ.mapCocone c.op)` using `isColimitOfPreserves Scheme.Γ hc.op`. Take `⟨hs, hi⟩` from `hB q (G.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c.op) hcol n i`.

Use `⟨fun x => ?_, fun j y hy => ?_⟩` and prove the remaining obligations. Take `⟨j', y', hy'⟩` from `hs (pull _ (sch.map c.pt.isoSpec.inv) _ n x) hu'`. Establish `h2 : pull _ (sch.map (Spec.map (c.π.app j'.unop).appTop)) _ n y' = pull _ (sch.map c.pt.isoSpec.inv) _ n x` using `hy'`. Use `⟨j'.unop, pull _ (sch.map (G.obj j'.unop).isoSpec.hom) _ n y', ?_⟩` and prove the remaining obligations. Use `(pull_comp_isoSpec_naturality (X := c.pt) (Y := G.obj j'.unop) _ _ n (c.π.app j'.unop) y').trans ?_` and prove the remaining obligations.

Rewrite using `[h2, pull_hom_pull_inv_eq_self]`. Establish `hz : pull _ (sch.map (Spec.map (c.π.app j).appTop)) _ n (pull _ (sch.map (G.obj j).isoSpec.inv) _ n y) = 0`. Establish `e : Spec.map (c.π.app j).appTop ≫ (G.obj j).isoSpec.inv = c.pt.isoSpec.inv ≫ c.π.app j`. Rewrite using `[Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Rewrite using `[pp, e, ← pp, hy, map_zero]`.

Take `⟨k', f', hk⟩` from `hi (op j) (pull _ (sch.map (G.obj j).isoSpec.inv) _ n y) (hu j) hz`. Use `⟨k'.unop, f'.unop, ?_⟩` and prove the remaining obligations. Establish `h3 : pull _ (sch.map (Spec.map (G.map f'.unop).appTop)) _ n (pull _ (sch.map (G.obj j).isoSpec.inv) _ n y) = 0` using `hk`. Establish `e` using `pull_comp_isoSpec_naturality _ (tw q i) n (G.map f'.unop) (pull _ (sch.map (G.obj j).isoSpec.inv) _ n y)`. Rewrite `e` using `[h3, map_zero, pull_hom_pull_inv_eq_self]`. Then use the resulting hypothesis.
-/
private theorem cont_aff (hB : B1) (q : ℕ) (i n : ℤ) {I : Type} [SmallCategory I] [IsCofiltered I]
    (G : I ⥤ Scheme.{0}) (c : Cone G) (hc : IsLimit c) (hG : ∀ j, IsAffine (G.obj j))
    (hu : ∀ j, IsUnit (q : Γ(G.obj j, ⊤))) (hu' : IsUnit (q : Γ(c.pt, ⊤))) :
    (∀ x : H (ZMod q) (sch.obj c.pt) (tw q i) n, ∃ (j : I) (y : H (ZMod q) (sch.obj (G.obj j)) (tw q i) n),
      pull _ (sch.map (c.π.app j)) _ n y = x) ∧
    ∀ (j : I) (y : H (ZMod q) (sch.obj (G.obj j)) (tw q i) n), pull _ (sch.map (c.π.app j)) _ n y = 0 →
      ∃ (k : I) (f : k ⟶ j), pull _ (sch.map (G.map f)) _ n y = 0 := by
  have hGo : ∀ j, IsAffine (G.op.obj j).unop := fun j => hG j.unop
  have hGi : ∀ j, IsAffine (G.obj j) := hG
  have hpt : IsAffine c.pt := Scheme.isAffine_of_isLimit c hc
  have hcol : IsColimit (Scheme.Γ.mapCocone c.op) := isColimitOfPreserves Scheme.Γ hc.op
  obtain ⟨hs, hi⟩ := hB q (G.op ⋙ Scheme.Γ) (Scheme.Γ.mapCocone c.op) hcol n i
  refine ⟨fun x => ?_, fun j y hy => ?_⟩
  · obtain ⟨j', y', hy'⟩ := hs (pull _ (sch.map c.pt.isoSpec.inv) _ n x) hu'
    have h2 : pull _ (sch.map (Spec.map (c.π.app j'.unop).appTop)) _ n y' =
        pull _ (sch.map c.pt.isoSpec.inv) _ n x := hy'
    refine ⟨j'.unop, pull _ (sch.map (G.obj j'.unop).isoSpec.hom) _ n y', ?_⟩
    refine (pull_comp_isoSpec_naturality (X := c.pt) (Y := G.obj j'.unop) _ _ n (c.π.app j'.unop) y').trans ?_
    rw [h2, pull_hom_pull_inv_eq_self]
  · have hz : pull _ (sch.map (Spec.map (c.π.app j).appTop)) _ n
        (pull _ (sch.map (G.obj j).isoSpec.inv) _ n y) = 0 := by
      have e : Spec.map (c.π.app j).appTop ≫ (G.obj j).isoSpec.inv = c.pt.isoSpec.inv ≫ c.π.app j := by
        rw [Iso.eq_inv_comp, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
          Iso.hom_inv_id, Category.comp_id]
      rw [pp, e, ← pp, hy, map_zero]
    obtain ⟨k', f', hk⟩ := hi (op j) (pull _ (sch.map (G.obj j).isoSpec.inv) _ n y) (hu j) hz
    refine ⟨k'.unop, f'.unop, ?_⟩
    have h3 : pull _ (sch.map (Spec.map (G.map f'.unop).appTop)) _ n
        (pull _ (sch.map (G.obj j).isoSpec.inv) _ n y) = 0 := hk
    have e := pull_comp_isoSpec_naturality _ (tw q i) n (G.map f'.unop) (pull _ (sch.map (G.obj j).isoSpec.inv) _ n y)
    rwa [h3, map_zero, pull_hom_pull_inv_eq_self] at e

end UpperTheory.Cb.TensorPullbackSquares

namespace UpperTheory.Cb.TensorPullbackSquares
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

private def tmP {I : Type} [SmallCategory I] (G : I ⥤ Scheme.{0}) {j : I} {W : Scheme.{0}} (v : W ⟶ G.obj j)
    {m' m : Over j} (g : m' ⟶ m) : pullback (G.map m'.hom) v ⟶ pullback (G.map m.hom) v :=
  tm v ((Over.post G).map g)

/- English proof (translation)
Establish `hG : ∀ {a b : I} (f : a ⟶ b), IsAffineHom (G.map f)` using `fun f => haff _ _ f`. Set `𝒰` to `(G.obj j).affineCover.finiteSubcover`. Establish `hX : ∀ a, IsAffine (𝒰.X a)` using `fun a => inferInstanceAs (IsAffine (Spec _))`. Set `U : 𝒰.I₀ → (G.obj j).Opens` to `fun a => (𝒰.f a).opensRange`. Establish `hU : ∀ a, IsAffineOpen (U a)` using `fun a => isAffineOpen_opensRange (𝒰.f a)`.

Establish `step : ∀ a, ∃ (k : Over j) (f : k ⟶ Over.mk (𝟙 j)), pull _ (sch.map ((AlgebraicGeometry.opensDiagram G j (U a)).map f)) _ 0 (pull _ (sch.map (Scheme.Opens.ι (G.map (Over.mk (𝟙 j)).hom ⁻¹ᵁ U a))) _ 0 y) = 0`. Introduce `a`. Establish `haf : ∀ k', IsAffine ((AlgebraicGeometry.opensDiagram G j (U a)).obj k')` using `fun k' => (hU a).preimage _`. Use `(cont_aff hB q i 0 (AlgebraicGeometry.opensDiagram G j (U a)) (AlgebraicGeometry.opensCone G c j (U a)) (AlgebraicGeometry.isLimitOpensCone G c hc j (U a)) haf ?_ ?_).2 (Over.mk (𝟙 j)) _ ?_` and prove the remaining obligations. Introduce `k'`.

Conclude with `hu _ k'.left (Scheme.Opens.ι _)`. Conclude with `hu _ j (Scheme.Opens.ι _ ≫ c.π.app j)`. Establish `e1 : (AlgebraicGeometry.opensCone G c j (U a)).π.app (Over.mk (𝟙 j)) ≫ Scheme.Opens.ι (G.map (Over.mk (𝟙 j)).hom ⁻¹ᵁ U a) = Scheme.Opens.ι (c.π.app j ⁻¹ᵁ U a) ≫ c.π.app j`. Simplify using `only [AlgebraicGeometry.opensCone_π_app]`. Conclude with `Scheme.Hom.resLE_comp_ι _ _`.

Establish `e2` using `pp (ZMod q) (tw q i) 0 ((AlgebraicGeometry.opensCone G c j (U a)).π.app (Over.mk (𝟙 j))) (Scheme.Opens.ι (G.map (Over.mk (𝟙 j)).hom ⁻¹ᵁ U a)) y`. Use `e2.trans ?_` and prove the remaining obligations. Rewrite using `[e1]`. Use `(pp (ZMod q) (tw q i) 0 (Scheme.Opens.ι (c.π.app j ⁻¹ᵁ U a)) (c.π.app j) y).symm.trans ?_` and prove the remaining obligations. Rewrite using `[hy]`.

Conclude with `map_zero _`. Use `choose k f hk using step`. Take `⟨m, hm⟩` from `IsCofiltered.inf_objs_exists (Finset.univ.image k)`. Establish `g : ∀ a, m ⟶ k a` using `fun a => (hm (by simp)).some`. Use `⟨m.left, m.hom, ?_⟩` and prove the remaining obligations.

Establish `e3 : ∀ a, (AlgebraicGeometry.opensDiagram G j (U a)).map (g a ≫ f a) ≫ Scheme.Opens.ι (G.map (Over.mk (𝟙 j)).hom ⁻¹ᵁ U a) = Scheme.Opens.ι (G.map m.hom ⁻¹ᵁ U a) ≫ G.map m.hom`. Introduce `a`. Rewrite using `[AlgebraicGeometry.opensDiagram_map]`. Use `(Scheme.Hom.resLE_comp_ι _ _).trans ?_` and prove the remaining obligations. Use `congr 2`.

Simplify using `using Over.w (g a ≫ f a)`. Establish `loc0 : ∀ a, pull _ (sch.map (Scheme.Opens.ι (G.map m.hom ⁻¹ᵁ U a))) _ 0 (pull _ (sch.map (G.map m.hom)) _ 0 y) = 0`. Introduce `a`. Use `(pp _ _ _ _ _ y).trans ?_` and prove the remaining obligations. Rewrite using `[← e3 a]`.

Use `(pp _ _ _ _ _ y).symm.trans ?_` and prove the remaining obligations. Rewrite using `[Functor.map_comp]`. Use `(pp _ _ _ _ _ _).symm.trans ?_` and prove the remaining obligations. Conclude with `(congrArg (pull _ (sch.map ((AlgebraicGeometry.opensDiagram G j (U a)).map (g a))) _ 0) (hk a)).trans (map_zero _)`. Take `⟨-, e, he1, -⟩` from `hA (ZMod q) (tw q i)`.

Use `set z := pull _ (sch.map (G.map m.hom)) _ 0 y with hz`. Establish `hs : (e (G.obj m.left)).symm z = 0`. Use `(sec_sep_glue_of_points (ZMod q) (tw q i) (G.obj m.left) 𝒰.I₀ (fun a => (G.map m.hom ⁻¹ᵁ U a : Scheme)) (fun a => Scheme.Opens.ι _) (fun a => inferInstance) ?_).1 _ ?_` and prove the remaining obligations. Introduce `u`. Take `⟨v, hv⟩` from `𝒰.covers (G.map m.hom u)`.

Use `⟨𝒰.idx (G.map m.hom u), ⟨u, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `⟨v, hv⟩`. Introduce `a`. Rewrite using `[← (e _).map_eq_zero_iff, ← he1, AddEquiv.apply_symm_apply]`. Conclude with `loc0 a`.

Rewrite using `[← (e (G.obj m.left)).symm.map_eq_zero_iff]`. Conclude with `hs`.
-/
private theorem cont_qc (hA : A9) (hB : B1) (q : ℕ) (i : ℤ) {I : Type} [SmallCategory I] [IsCofiltered I]
    (G : I ⥤ Scheme.{0}) (c : Cone G) (hc : IsLimit c) (hcomp : ∀ j, CompactSpace (G.obj j))
    (haff : ∀ (j k : I) (f : j ⟶ k), IsAffineHom (G.map f))
    (hu : ∀ (Z : Scheme.{0}) (j : I), (Z ⟶ G.obj j) → IsUnit (q : Γ(Z, ⊤))) (j : I)
    (y : H (ZMod q) (sch.obj (G.obj j)) (tw q i) 0) (hy : pull _ (sch.map (c.π.app j)) _ 0 y = 0) :
    ∃ (k : I) (f : k ⟶ j), pull _ (sch.map (G.map f)) _ 0 y = 0 := by
  classical
  have hG : ∀ {a b : I} (f : a ⟶ b), IsAffineHom (G.map f) := fun f => haff _ _ f
  let 𝒰 := (G.obj j).affineCover.finiteSubcover
  have hX : ∀ a, IsAffine (𝒰.X a) := fun a => inferInstanceAs (IsAffine (Spec _))
  let U : 𝒰.I₀ → (G.obj j).Opens := fun a => (𝒰.f a).opensRange
  have hU : ∀ a, IsAffineOpen (U a) := fun a => isAffineOpen_opensRange (𝒰.f a)
  have step : ∀ a, ∃ (k : Over j) (f : k ⟶ Over.mk (𝟙 j)),
      pull _ (sch.map ((AlgebraicGeometry.opensDiagram G j (U a)).map f)) _ 0
        (pull _ (sch.map (Scheme.Opens.ι (G.map (Over.mk (𝟙 j)).hom ⁻¹ᵁ U a))) _ 0 y) = 0 := by
    intro a
    have haf : ∀ k', IsAffine ((AlgebraicGeometry.opensDiagram G j (U a)).obj k') :=
      fun k' => (hU a).preimage _
    refine (cont_aff hB q i 0 (AlgebraicGeometry.opensDiagram G j (U a))
      (AlgebraicGeometry.opensCone G c j (U a)) (AlgebraicGeometry.isLimitOpensCone G c hc j (U a))
      haf ?_ ?_).2 (Over.mk (𝟙 j)) _ ?_
    · intro k'
      exact hu _ k'.left (Scheme.Opens.ι _)
    · exact hu _ j (Scheme.Opens.ι _ ≫ c.π.app j)
    · have e1 : (AlgebraicGeometry.opensCone G c j (U a)).π.app (Over.mk (𝟙 j)) ≫
          Scheme.Opens.ι (G.map (Over.mk (𝟙 j)).hom ⁻¹ᵁ U a) =
          Scheme.Opens.ι (c.π.app j ⁻¹ᵁ U a) ≫ c.π.app j := by
        simp only [AlgebraicGeometry.opensCone_π_app]
        exact Scheme.Hom.resLE_comp_ι _ _
      have e2 := pp (ZMod q) (tw q i) 0 ((AlgebraicGeometry.opensCone G c j (U a)).π.app (Over.mk (𝟙 j)))
        (Scheme.Opens.ι (G.map (Over.mk (𝟙 j)).hom ⁻¹ᵁ U a)) y
      refine e2.trans ?_
      rw [e1]
      refine (pp (ZMod q) (tw q i) 0 (Scheme.Opens.ι (c.π.app j ⁻¹ᵁ U a)) (c.π.app j) y).symm.trans ?_
      rw [hy]
      exact map_zero _
  choose k f hk using step
  obtain ⟨m, hm⟩ := IsCofiltered.inf_objs_exists (Finset.univ.image k)
  have g : ∀ a, m ⟶ k a := fun a => (hm (by simp)).some
  refine ⟨m.left, m.hom, ?_⟩
  have e3 : ∀ a, (AlgebraicGeometry.opensDiagram G j (U a)).map (g a ≫ f a) ≫
      Scheme.Opens.ι (G.map (Over.mk (𝟙 j)).hom ⁻¹ᵁ U a) =
      Scheme.Opens.ι (G.map m.hom ⁻¹ᵁ U a) ≫ G.map m.hom := by
    intro a
    rw [AlgebraicGeometry.opensDiagram_map]
    refine (Scheme.Hom.resLE_comp_ι _ _).trans ?_
    congr 2
    simpa using Over.w (g a ≫ f a)
  have loc0 : ∀ a, pull _ (sch.map (Scheme.Opens.ι (G.map m.hom ⁻¹ᵁ U a))) _ 0
      (pull _ (sch.map (G.map m.hom)) _ 0 y) = 0 := by
    intro a
    refine (pp _ _ _ _ _ y).trans ?_
    rw [← e3 a]
    refine (pp _ _ _ _ _ y).symm.trans ?_
    rw [Functor.map_comp]
    refine (pp _ _ _ _ _ _).symm.trans ?_
    exact (congrArg (pull _ (sch.map ((AlgebraicGeometry.opensDiagram G j (U a)).map (g a))) _ 0)
      (hk a)).trans (map_zero _)
  obtain ⟨-, e, he1, -⟩ := hA (ZMod q) (tw q i)
  set z := pull _ (sch.map (G.map m.hom)) _ 0 y with hz
  have hs : (e (G.obj m.left)).symm z = 0 := by
    refine (sec_sep_glue_of_points (ZMod q) (tw q i) (G.obj m.left) 𝒰.I₀
      (fun a => (G.map m.hom ⁻¹ᵁ U a : Scheme)) (fun a => Scheme.Opens.ι _) (fun a => inferInstance) ?_).1 _ ?_
    · intro u
      obtain ⟨v, hv⟩ := 𝒰.covers (G.map m.hom u)
      refine ⟨𝒰.idx (G.map m.hom u), ⟨u, ?_⟩, rfl⟩
      exact ⟨v, hv⟩
    · intro a
      rw [← (e _).map_eq_zero_iff, ← he1, AddEquiv.apply_symm_apply]
      exact loc0 a
  rw [← (e (G.obj m.left)).symm.map_eq_zero_iff]
  exact hs

/- English proof (translation)
Take `⟨I, _, _, G, π, ⟨hl⟩, hG⟩` from `GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' S O s hs`. Establish `hl1 : IsLimit ((Over.forget S).mapCone ⟨Over.mk s, π⟩)` using `isLimitOfPreserves (Over.forget S) hl`. Establish `hl2 : IsLimit ((TF r).mapCone ⟨Over.mk s, π⟩)` using `isLimitOfPreserves (TF r) hl`. Take `⟨j0, y, hy⟩` from `(cont_aff hB q i 0 (G ⋙ Over.forget S) _ hl1 (fun j => (hG j).1) (fun j => hu _ (G.obj j).hom) (hu _ s)).1 c`. Establish `hy' : pull _ (sch.map (π.app j0).left) _ 0 y = c` using `hy`.

Establish `hcomp : ∀ j, CompactSpace ((G ⋙ TF r).obj j)`. Introduce `j`. Use `(hG j).1` as an intermediate fact. Establish `hq : QuasiCompact (pullback.fst (G.obj j).hom r)` using `MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _).flip inferInstance`. Conclude with `@QuasiCompact.compactSpace_of_compactSpace _ _ _ hq inferInstance`.

Establish `haff : ∀ (j k : I) (f : j ⟶ k), IsAffineHom ((G ⋙ TF r).map f)`. Introduce `j k f`. Use `(hG j).1` as an intermediate fact. Use `(hG k).1` as an intermediate fact. Conclude with `MorphismProperty.of_isPullback (P := @IsAffineHom) (tm_isPullback r (G.map f)).flip inferInstance`.

Establish `hu2 : ∀ (Z : Scheme.{0}) (j : I), (Z ⟶ (G ⋙ TF r).obj j) → IsUnit (q : Γ(Z, ⊤))` using `fun Z j h => hu Z (h ≫ pullback.fst _ _ ≫ (G.obj j).hom)`. Establish `hδ : pull _ (sch.map (((TF r).mapCone ⟨Over.mk s, π⟩).π.app j0)) _ 0 (pull _ (sch.map (pullback.fst (G.obj j0).hom r)) _ 0 y - pull _ (sch.map (pullback.snd (G.obj j0).hom r)) _ 0 w) = 0`. Express the relevant statement in the definitionally equal form `pull _ (sch.map (tm r (π.app j0))) _ 0 _ = 0`. Use `erw [map_sub, pp, pp, tm_fst, tm_snd, ← pp, hy']`. Conclude with `sub_eq_zero.mpr hc`.

Take `⟨k, f, hk⟩` from `cont_qc hA hB q i (G ⋙ TF r) _ hl2 hcomp haff hu2 j0 _ hδ`. Use `⟨G.obj k, (π.app k).left, pull _ (sch.map (G.map f).left) _ 0 y, ?_, (hG k).2, ?_⟩` and prove the remaining obligations. Simplify using `using Over.w (π.app k)`. Express the relevant statement in the definitionally equal form `pull _ (sch.map (tm r (G.map f))) _ 0 _ = 0 at hk erw [map_sub, pp, pp, tm_fst, tm_snd, ← pp] at hk`. Conclude with `sub_eq_zero.mp hk`.
-/
private theorem cont_step (hA : A9) (hB : B1) (q : ℕ) (i : ℤ) {S X : Scheme.{0}} (r : X ⟶ S) [QuasiCompact r]
    (hu : ∀ (Z : Scheme.{0}), (Z ⟶ S) → IsUnit (q : Γ(Z, ⊤)))
    (O : Type) [CommRing O] (s : Spec (CommRingCat.of O) ⟶ S)
    (hs : IsStalk O s) (w : H (ZMod q) (sch.obj X) (tw q i) 0)
    (c : H (ZMod q) (sch.obj (Spec (CommRingCat.of O))) (tw q i) 0)
    (hc : pull _ (sch.map (pullback.fst s r)) _ 0 c = pull _ (sch.map (pullback.snd s r)) _ 0 w) :
    ∃ (Z : Over S) (j : Spec (CommRingCat.of O) ⟶ Z.left) (d : H (ZMod q) (sch.obj Z.left) (tw q i) 0),
      j ≫ Z.hom = s ∧ Etale Z.hom ∧
      pull _ (sch.map (pullback.fst Z.hom r)) _ 0 d = pull _ (sch.map (pullback.snd Z.hom r)) _ 0 w := by
  obtain ⟨I, _, _, G, π, ⟨hl⟩, hG⟩ := GlobalTheory.T.exists_cofiltered_limit_affine_etale_of_isStalk' S O s hs
  have hl1 : IsLimit ((Over.forget S).mapCone ⟨Over.mk s, π⟩) := isLimitOfPreserves (Over.forget S) hl
  have hl2 : IsLimit ((TF r).mapCone ⟨Over.mk s, π⟩) := isLimitOfPreserves (TF r) hl
  obtain ⟨j0, y, hy⟩ := (cont_aff hB q i 0 (G ⋙ Over.forget S) _ hl1 (fun j => (hG j).1)
    (fun j => hu _ (G.obj j).hom) (hu _ s)).1 c
  have hy' : pull _ (sch.map (π.app j0).left) _ 0 y = c := hy
  have hcomp : ∀ j, CompactSpace ((G ⋙ TF r).obj j) := by
    intro j
    have := (hG j).1
    have hq : QuasiCompact (pullback.fst (G.obj j).hom r) :=
      MorphismProperty.of_isPullback (P := @QuasiCompact) (IsPullback.of_hasPullback _ _).flip inferInstance
    exact @QuasiCompact.compactSpace_of_compactSpace _ _ _ hq inferInstance
  have haff : ∀ (j k : I) (f : j ⟶ k), IsAffineHom ((G ⋙ TF r).map f) := by
    intro j k f
    have := (hG j).1
    have := (hG k).1
    exact MorphismProperty.of_isPullback (P := @IsAffineHom) (tm_isPullback r (G.map f)).flip inferInstance
  have hu2 : ∀ (Z : Scheme.{0}) (j : I), (Z ⟶ (G ⋙ TF r).obj j) → IsUnit (q : Γ(Z, ⊤)) :=
    fun Z j h => hu Z (h ≫ pullback.fst _ _ ≫ (G.obj j).hom)
  have hδ : pull _ (sch.map (((TF r).mapCone ⟨Over.mk s, π⟩).π.app j0)) _ 0
      (pull _ (sch.map (pullback.fst (G.obj j0).hom r)) _ 0 y -
        pull _ (sch.map (pullback.snd (G.obj j0).hom r)) _ 0 w) = 0 := by
    change pull _ (sch.map (tm r (π.app j0))) _ 0 _ = 0
    erw [map_sub, pp, pp, tm_fst, tm_snd, ← pp, hy']
    exact sub_eq_zero.mpr hc
  obtain ⟨k, f, hk⟩ := cont_qc hA hB q i (G ⋙ TF r) _ hl2 hcomp haff hu2 j0 _ hδ
  refine ⟨G.obj k, (π.app k).left, pull _ (sch.map (G.map f).left) _ 0 y, ?_, (hG k).2, ?_⟩
  · simpa using Over.w (π.app k)
  · change pull _ (sch.map (tm r (G.map f))) _ 0 _ = 0 at hk
    erw [map_sub, pp, pp, tm_fst, tm_snd, ← pp] at hk
    exact sub_eq_zero.mp hk

end UpperTheory.Cb.TensorPullbackSquares

namespace UpperTheory.Cb.TensorPullbackSquares
open LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut

/- English proof (translation)
Take `⟨O, hO, s, g, hs, v, hv⟩` from `GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point U.left (Over.mk (𝟙 U.left)) (by dsimp; infer_instance) x`. Establish `hsg : g.left = s` using `by simpa using Over.w g`. Use `haveI hr : QuasiCompact (toBY P U) := by dsimp [toBY]; infer_instance`. Establish `hu : ∀ (Z : Scheme.{0}), (Z ⟶ U.left) → IsUnit (q : Γ(Z, ⊤))` using `fun Z g' => unit_of hq (g' ≫ U.hom ≫ toK)`. Establish `hrange : Set.range (s ≫ U.hom) ⊆ (V : Set B)`.

Introduce and unpack `_ ⟨z, rfl⟩`. Conclude with `hU (s z)`. Set `n : pullback P (s ≫ U.hom) ⟶ YU P U` to `pullback.lift (pullback.fst P (s ≫ U.hom)) (pullback.snd P (s ≫ U.hom) ≫ s) (by rw [pullback.condition, Category.assoc])`. Set `m : pullback s (toBY P U) ⟶ pullback P (s ≫ U.hom)` to `pullback.lift (pullback.snd s (toBY P U) ≫ pullback.fst P U.hom) (pullback.fst s (toBY P U)) (by rw [Category.assoc, pullback.condition, ← Category.assoc, ← pullback.condition, Category.assoc])`. Establish `hn1 : n ≫ pullback.fst P U.hom = pullback.fst P (s ≫ U.hom)` using `by erw [pullback.lift_fst]`.

Establish `hn2 : n ≫ pullback.snd P U.hom = pullback.snd P (s ≫ U.hom) ≫ s` using `by erw [pullback.lift_snd]`. Establish `hm1 : m ≫ pullback.fst P (s ≫ U.hom) = pullback.snd s (toBY P U) ≫ pullback.fst P U.hom` using `by erw [pullback.lift_fst]`. Establish `hm2 : m ≫ pullback.snd P (s ≫ U.hom) = pullback.fst s (toBY P U)` using `by erw [pullback.lift_snd]`. Establish `hmn : m ≫ n = pullback.snd s (toBY P U)`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, hn1, hm1]`. Rewrite using `[Category.assoc, hn2, ← Category.assoc, hm2]`. Conclude with `pullback.condition`. Take `⟨c0, hc0⟩` from `(hS O (s ≫ U.hom) hs.1 hrange).2 (pull (ZMod q) (sch.map n) (tw q i) 0 w)`. Establish `hc : pull _ (sch.map (pullback.fst s (toBY P U))) _ 0 c0 = pull _ (sch.map (pullback.snd s (toBY P U))) _ 0 w`.

Rewrite using `[← hm2, ← pp]`. Express the relevant statement in the definitionally equal form `pull _ (sch.map m) _ 0 (pl q i (pullback.snd P (s ≫ U.hom)) 0 c0) = _`. Rewrite using `[hc0, pp, hmn]`. Take `⟨Z, j, d, hj, hZ, hd⟩` from `cont_step hA hB q i (toBY P U) hu O s hs w c0 hc`. Use `haveI := hZ`.

Use `haveI : Etale U.hom := U.prop`. Set `U' : B.Etale` to `MorphismProperty.Over.mk ⊤ (Z.hom ≫ U.hom) inferInstance`. Set `a : U' ⟶ U` to `MorphismProperty.Over.homMk Z.hom rfl trivial`. Use `⟨U', a, d, ⟨j v, ?_⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Z.hom (j v) = x`.

Rewrite using `[← Scheme.Hom.comp_apply, hj, ← hsg, hv]`. Establish `hcomm : toBY P U' ≫ Z.hom = resY P a ≫ toBY P U`. Simplify using `only [resY, toBY]`. Use `erw [pullback.lift_snd]`. Both sides reduce to the same expression.

Set `ψ : YU P U' ⟶ pullback Z.hom (toBY P U)` to `pullback.lift (toBY P U') (resY P a) hcomm`. Establish `hψ1 : ψ ≫ pullback.fst Z.hom (toBY P U) = toBY P U'` using `pullback.lift_fst _ _ _`. Establish `hψ2 : ψ ≫ pullback.snd Z.hom (toBY P U) = resY P a` using `pullback.lift_snd _ _ _`. Rewrite using `[← hψ1, ← hψ2]`. Conclude with `(pp (ZMod q) (tw q i) 0 ψ _ d).symm.trans ((congrArg _ hd).trans (pp (ZMod q) (tw q i) 0 ψ _ w))`.
-/
private theorem locAbs (hA : A9) (hB : B1) (q : ℕ) (i : ℤ) {k : Type} [Field k] (hq : IsUnit (q : k))
    {B Y : Scheme.{0}} (toK : B ⟶ Sp k) (P : Y ⟶ B) [IsProper P] (V : B.Opens)
    (hS : ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
      Function.Bijective (pl q i (pullback.snd P t) 0))
    (U : B.Etale) (hU : ∀ u : U.left, U.hom u ∈ V) (w : H (ZMod q) (sch.obj (YU P U)) (tw q i) 0)
    (x : U.left) :
    ∃ (U' : B.Etale) (a : U' ⟶ U) (c : H (ZMod q) (sch.obj U'.left) (tw q i) 0), x ∈ Set.range a.left ∧
      pull _ (sch.map (toBY P U')) _ 0 c = pull _ (sch.map (resY P a)) _ 0 w := by
  obtain ⟨O, hO, s, g, hs, v, hv⟩ := GlobalTheory.T.exists_strictlyHenselianEtaleStalk_over_point U.left (Over.mk (𝟙 U.left)) (by dsimp; infer_instance) x
  have hsg : g.left = s := by simpa using Over.w g
  haveI hr : QuasiCompact (toBY P U) := by dsimp [toBY]; infer_instance
  have hu : ∀ (Z : Scheme.{0}), (Z ⟶ U.left) → IsUnit (q : Γ(Z, ⊤)) := fun Z g' => unit_of hq (g' ≫ U.hom ≫ toK)
  have hrange : Set.range (s ≫ U.hom) ⊆ (V : Set B) := by
    rintro _ ⟨z, rfl⟩
    exact hU (s z)
  let n : pullback P (s ≫ U.hom) ⟶ YU P U :=
    pullback.lift (pullback.fst P (s ≫ U.hom)) (pullback.snd P (s ≫ U.hom) ≫ s)
      (by rw [pullback.condition, Category.assoc])
  let m : pullback s (toBY P U) ⟶ pullback P (s ≫ U.hom) :=
    pullback.lift (pullback.snd s (toBY P U) ≫ pullback.fst P U.hom) (pullback.fst s (toBY P U))
      (by rw [Category.assoc, pullback.condition, ← Category.assoc, ← pullback.condition, Category.assoc])
  have hn1 : n ≫ pullback.fst P U.hom = pullback.fst P (s ≫ U.hom) := by
    erw [pullback.lift_fst]
  have hn2 : n ≫ pullback.snd P U.hom = pullback.snd P (s ≫ U.hom) ≫ s := by
    erw [pullback.lift_snd]
  have hm1 : m ≫ pullback.fst P (s ≫ U.hom) = pullback.snd s (toBY P U) ≫ pullback.fst P U.hom := by
    erw [pullback.lift_fst]
  have hm2 : m ≫ pullback.snd P (s ≫ U.hom) = pullback.fst s (toBY P U) := by
    erw [pullback.lift_snd]
  have hmn : m ≫ n = pullback.snd s (toBY P U) := by
    apply pullback.hom_ext
    · rw [Category.assoc, hn1, hm1]
    · rw [Category.assoc, hn2, ← Category.assoc, hm2]
      exact pullback.condition
  obtain ⟨c0, hc0⟩ := (hS O (s ≫ U.hom) hs.1 hrange).2 (pull (ZMod q) (sch.map n) (tw q i) 0 w)
  have hc : pull _ (sch.map (pullback.fst s (toBY P U))) _ 0 c0 =
      pull _ (sch.map (pullback.snd s (toBY P U))) _ 0 w := by
    rw [← hm2, ← pp]
    change pull _ (sch.map m) _ 0 (pl q i (pullback.snd P (s ≫ U.hom)) 0 c0) = _
    rw [hc0, pp, hmn]
  obtain ⟨Z, j, d, hj, hZ, hd⟩ := cont_step hA hB q i (toBY P U) hu O s hs w c0 hc
  haveI := hZ
  haveI : Etale U.hom := U.prop
  let U' : B.Etale := MorphismProperty.Over.mk ⊤ (Z.hom ≫ U.hom) inferInstance
  let a : U' ⟶ U := MorphismProperty.Over.homMk Z.hom rfl trivial
  refine ⟨U', a, d, ⟨j v, ?_⟩, ?_⟩
  · change Z.hom (j v) = x
    rw [← Scheme.Hom.comp_apply, hj, ← hsg, hv]
  · have hcomm : toBY P U' ≫ Z.hom = resY P a ≫ toBY P U := by
      simp only [resY, toBY]
      erw [pullback.lift_snd]
      rfl
    let ψ : YU P U' ⟶ pullback Z.hom (toBY P U) := pullback.lift (toBY P U') (resY P a) hcomm
    have hψ1 : ψ ≫ pullback.fst Z.hom (toBY P U) = toBY P U' := pullback.lift_fst _ _ _
    have hψ2 : ψ ≫ pullback.snd Z.hom (toBY P U) = resY P a := pullback.lift_snd _ _ _
    rw [← hψ1, ← hψ2]
    exact (pp (ZMod q) (tw q i) 0 ψ _ d).symm.trans ((congrArg _ hd).trans (pp (ZMod q) (tw q i) 0 ψ _ w))

end UpperTheory.Cb.TensorPullbackSquares

open UpperTheory.Cb.TensorPullbackSquares LateralTheory.E.E4 LateralTheory.E.LeafGhostCut LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut in
/- English proof (translation)
Introduce `hyps q _ k _ hq i B W Y0 Y1 Y2 x0 ι _ V hV p g1 g2 hp hp1 hP hSHV U y u hu`. Take `⟨-, -, -, -, -, -, -, hA, -, -, hB, -⟩` from `hyps`. Use `haveI : IsProper (g2 ≫ g1 ≫ p) := hP`. Establish `hS : ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V → Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)` using `fun A _ t hA' ht => (hSHV A t hA' ht).2.2.2`. Set `V' : U.left.Opens` to `U.hom ⁻¹ᵁ V`.

Set `U0 : B.Etale` to `MorphismProperty.Over.mk ⊤ (V'.ι ≫ U.hom) inferInstance`. Set `inc : U0 ⟶ U` to `MorphismProperty.Over.homMk V'.ι rfl trivial`. Establish `hU0 : ∀ v : U0.left, U0.hom v ∈ V`. Introduce `v`. Establish `h2 : U0.hom v = U.hom (V'.ι v)` using `Scheme.Hom.comp_apply V'.ι U.hom v`.

Rewrite using `[h2]`. Establish `h1 : V'.ι v ∈ (V' : Set U.left)`. Rewrite using `[← Scheme.Opens.range_ι]`. Conclude with `⟨v, rfl⟩`. Conclude with `h1`.

Choose the witnesses or unpack the hypotheses as in `⟨u0, hu0⟩ : u ∈ Set.range V'.ι := by`. Rewrite using `[Scheme.Opens.range_ι]`. Conclude with `hu`. Take `⟨U', a, c, hxa, hc⟩` from `locAbs hA hB q i hq x0 (g2 ≫ g1 ≫ p) V hS U0 hU0 (pull _ (sch.map (resY (g2 ≫ g1 ≫ p) inc)) _ 0 (fgt (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0 y)) u0`. Use `⟨U', a ≫ inc, ?_, ?_⟩` and prove the remaining obligations.

Take `⟨z, hz⟩` from `hxa`. Use `⟨z, ?_⟩` and prove the remaining obligations. Establish `h3 : (a ≫ inc).left z = V'.ι (a.left z)` using `Scheme.Hom.comp_apply a.left V'.ι z`. Rewrite using `[h3, hz, hu0]`. Introduce `U'' b`.

Establish `hb : b.left ≫ U'.hom = U''.hom` using `by simpa using b.w`. Establish `ha : a.left ≫ U0.hom = U'.hom` using `by simpa using a.w`. Establish `hV'' : ∀ t : U''.left, U''.hom t ∈ V`. Introduce `t`. Rewrite using `[← hb, Scheme.Hom.comp_apply, ← ha, Scheme.Hom.comp_apply]`.

Conclude with `hU0 _`. Establish `hemp : IsEmpty (pullback (C` using `Scheme.{0}) U''.hom ι) := by`. Prove the components needed by the constructor for the conclusion. Introduce `z`. Establish `e1 : (pullback.fst U''.hom ι ≫ U''.hom) z = (pullback.snd U''.hom ι ≫ ι) z`.

Rewrite using `[pullback.condition]`. Establish `hv` using `hV'' (pullback.fst U''.hom ι z)`. Rewrite `e1` using `[Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]`. Rewrite `hv` using `[e1]`. Establish `hv' : ι (pullback.snd U''.hom ι z) ∈ (V : Set B)` using `hv`.

Rewrite `hv'` using `[hV]`. Conclude with `hv' ⟨_, rfl⟩`. Establish `hsub : Subsingleton (H (ZMod q) (sch.obj (pullback U''.hom ι)) (tw q i) 0)`. Take `⟨-, e, -, -⟩` from `hA (ZMod q) (tw q i)`. Use `haveI := LateralTheory.EDual.sec_empty_sub (tw q i) (pullback U''.hom ι)`.

Conclude with `(e _).symm.injective.subsingleton`. Take `⟨c'', hc''⟩` from `relExact (ZMod q) (tw q i) (sch.map (prB ι U'')) 0 (pull (ZMod q) (sch.map b.left) (tw q i) 0 c) (Subsingleton.elim _ _)`. Use `⟨c'', ?_⟩` and prove the remaining obligations. Establish `hsubm : Subsingleton (H (ZMod q) (sch.obj (pullback (pullback.snd (g2 ≫ g1 ≫ p) U''.hom ≫ U''.hom) ι)) (tw q i) (-1))` using `(hA (ZMod q) (tw q i)).1 _ (-1) (by norm_num)`. Rewrite using `[← sub_eq_zero]`.

Apply `LateralTheory.E.LeafInj0VPf.relative_cohomology_forget_injective_degree_zero_of_subsingleton _ _ _ hsubm` to reduce the goal to its premises. Rewrite using `[map_sub, sub_eq_zero]`. Simplify using `only [bY, rY, rpl]`. Rewrite using `[relNat, relNat, hc'', pp]`. Establish `e2 : toBY (g2 ≫ g1 ≫ p) U'' ≫ b.left = resY (g2 ≫ g1 ≫ p) b ≫ toBY (g2 ≫ g1 ≫ p) U'`.

Conclude with `(pullback.lift_snd _ _ _).symm`. Rewrite using `[e2, ← pp, hc, pp, pp, ← LateralTheory.E.SecondDegreeKilling.Nbhd.resY_comp, ← LateralTheory.E.SecondDegreeKilling.Nbhd.resY_comp, Category.assoc]`.
-/
theorem UpperTheory.Cb.etale_cohomology_degree_zero_surjective_limit :
    LateralTheory.E.LeafSurj0Pf.LeafSurj0V := by
  intro hyps q _ k _ hq i B W Y0 Y1 Y2 x0 ι _ V hV p g1 g2 hp hp1 hP hSHV U y u hu
  obtain ⟨-, -, -, -, -, -, -, hA, -, -, hB, -⟩ := hyps
  haveI : IsProper (g2 ≫ g1 ≫ p) := hP
  have hS : ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
      Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0) :=
    fun A _ t hA' ht => (hSHV A t hA' ht).2.2.2
  let V' : U.left.Opens := U.hom ⁻¹ᵁ V
  let U0 : B.Etale := MorphismProperty.Over.mk ⊤ (V'.ι ≫ U.hom) inferInstance
  let inc : U0 ⟶ U := MorphismProperty.Over.homMk V'.ι rfl trivial
  have hU0 : ∀ v : U0.left, U0.hom v ∈ V := by
    intro v
    have h2 : U0.hom v = U.hom (V'.ι v) := Scheme.Hom.comp_apply V'.ι U.hom v
    rw [h2]
    have h1 : V'.ι v ∈ (V' : Set U.left) := by
      rw [← Scheme.Opens.range_ι]
      exact ⟨v, rfl⟩
    exact h1
  obtain ⟨u0, hu0⟩ : u ∈ Set.range V'.ι := by
    rw [Scheme.Opens.range_ι]
    exact hu
  obtain ⟨U', a, c, hxa, hc⟩ := locAbs hA hB q i hq x0 (g2 ≫ g1 ≫ p) V hS U0 hU0
    (pull _ (sch.map (resY (g2 ≫ g1 ≫ p) inc)) _ 0
      (fgt (ZMod q) (sch.map (prU (g2 ≫ g1 ≫ p) ι U)) (tw q i) 0 y)) u0
  refine ⟨U', a ≫ inc, ?_, ?_⟩
  · obtain ⟨z, hz⟩ := hxa
    refine ⟨z, ?_⟩
    have h3 : (a ≫ inc).left z = V'.ι (a.left z) := Scheme.Hom.comp_apply a.left V'.ι z
    rw [h3, hz, hu0]
  · intro U'' b
    have hb : b.left ≫ U'.hom = U''.hom := by simpa using b.w
    have ha : a.left ≫ U0.hom = U'.hom := by simpa using a.w
    have hV'' : ∀ t : U''.left, U''.hom t ∈ V := by
      intro t
      rw [← hb, Scheme.Hom.comp_apply, ← ha, Scheme.Hom.comp_apply]
      exact hU0 _
    have hemp : IsEmpty (pullback (C := Scheme.{0}) U''.hom ι) := by
      constructor
      intro z
      have e1 : (pullback.fst U''.hom ι ≫ U''.hom) z = (pullback.snd U''.hom ι ≫ ι) z := by
        rw [pullback.condition]
      have hv := hV'' (pullback.fst U''.hom ι z)
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply] at e1
      rw [e1] at hv
      have hv' : ι (pullback.snd U''.hom ι z) ∈ (V : Set B) := hv
      rw [hV] at hv'
      exact hv' ⟨_, rfl⟩
    have hsub : Subsingleton (H (ZMod q) (sch.obj (pullback U''.hom ι)) (tw q i) 0) := by
      obtain ⟨-, e, -, -⟩ := hA (ZMod q) (tw q i)
      haveI := LateralTheory.EDual.sec_empty_sub (tw q i) (pullback U''.hom ι)
      exact (e _).symm.injective.subsingleton
    obtain ⟨c'', hc''⟩ := relExact (ZMod q) (tw q i) (sch.map (prB ι U'')) 0
      (pull (ZMod q) (sch.map b.left) (tw q i) 0 c) (Subsingleton.elim _ _)
    refine ⟨c'', ?_⟩
    have hsubm : Subsingleton (H (ZMod q)
        (sch.obj (pullback (pullback.snd (g2 ≫ g1 ≫ p) U''.hom ≫ U''.hom) ι)) (tw q i) (-1)) :=
      (hA (ZMod q) (tw q i)).1 _ (-1) (by norm_num)
    rw [← sub_eq_zero]
    apply LateralTheory.E.LeafInj0VPf.relative_cohomology_forget_injective_degree_zero_of_subsingleton _ _ _ hsubm
    rw [map_sub, sub_eq_zero]
    simp only [bY, rY, rpl]
    rw [relNat, relNat, hc'', pp]
    have e2 : toBY (g2 ≫ g1 ≫ p) U'' ≫ b.left = resY (g2 ≫ g1 ≫ p) b ≫ toBY (g2 ≫ g1 ≫ p) U' := by
      exact (pullback.lift_snd _ _ _).symm
    rw [e2, ← pp, hc, pp, pp, ← LateralTheory.E.SecondDegreeKilling.Nbhd.resY_comp, ← LateralTheory.E.SecondDegreeKilling.Nbhd.resY_comp, Category.assoc]
