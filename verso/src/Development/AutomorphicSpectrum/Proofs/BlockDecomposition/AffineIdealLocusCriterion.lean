import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.TrivLoc.Glue

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `(h (A ⧸ J) (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])` as an intermediate fact. Rewrite `this` using `[Ideal.mk_ker]`. Then use the resulting hypothesis. Use `(h (A ⧸ I) (Ideal.Quotient.mk I)).1 (by rw [Ideal.mk_ker])` as an intermediate fact. Rewrite `this` using `[Ideal.mk_ker]`. Then use the resulting hypothesis.
-/
theorem ideal_eq_of_le_ker_iff {A : Type} [CommRing A] {I J : Ideal A}
    (h : ∀ (R : Type) [CommRing R] (g : A →+* R), I ≤ RingHom.ker g ↔ J ≤ RingHom.ker g) :
    I = J := by
  apply le_antisymm
  · have := (h (A ⧸ J) (Ideal.Quotient.mk J)).2 (by rw [Ideal.mk_ker])
    rwa [Ideal.mk_ker] at this
  · have := (h (A ⧸ I) (Ideal.Quotient.mk I)).1 (by rw [Ideal.mk_ker])
    rwa [Ideal.mk_ker] at this

/- English proof (translation)
Use `TopCat.Presheaf.section_ext T.sheaf V s 0 fun x hx => ?_` and prove the remaining obligations. Take `⟨W, hW, hxW, hWV⟩` from `exists_isAffineOpen_mem_and_subset hx`. Establish `hz` using `h W hW hWV`. Establish `h1` using `TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hWV) x hxW s`. Use `h1.symm.trans ?_` and prove the remaining obligations.

Use `erw [hz, map_zero, map_zero]`. Both sides reduce to the same expression.
-/
theorem eq_zero_of_affine_restrict {T : Scheme.{0}} {V : T.Opens} (s : Γ(T, V))
    (h : ∀ (W : T.Opens) (_ : IsAffineOpen W) (e : W ≤ V),
      (T.presheaf.map (homOfLE e).op).hom s = 0) : s = 0 := by
  refine TopCat.Presheaf.section_ext T.sheaf V s 0 fun x hx => ?_
  obtain ⟨W, hW, hxW, hWV⟩ := exists_isAffineOpen_mem_and_subset hx
  have hz := h W hW hWV
  have h1 := TopCat.Presheaf.germ_res_apply T.presheaf (homOfLE hWV) x hxW s
  refine h1.symm.trans ?_
  erw [hz, map_zero, map_zero]
  rfl

/- English proof (translation)
Use `choose J hJ using rep`. Establish `hJ' : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (R : CommRingCat.{0}) (g : Γ(Y, U) ⟶ R), P (Spec R) (Spec.map g ≫ hU.fromSpec) ↔ J U hU ≤ RingHom.ker g.hom` using `fun U hU R g => hJ U hU R g.hom`. Set `I : Y.IdealSheafData` to `{ ideal := fun U => J U.1 U.2 map_ideal_basicOpen := by`. Introduce `U f`. Use `ideal_eq_of_le_ker_iff fun R _ g => ?_` and prove the remaining obligations.

Rewrite using `[Ideal.map_le_iff_le_comap, RingHom.comap_ker]`. Use `(hJ U.1 U.2 R _).symm.trans (Iff.trans ?_ (hJ _ (Y.affineBasicOpen f).2 R g))` and prove the remaining obligations. Establish `e` using `U.2.map_fromSpec (Y.affineBasicOpen f).2 (homOfLE (Y.basicOpen_le f)).op`. Rewrite using `[← e, ← Category.assoc, ← Spec.map_comp]`. Use `rfl }`.

Establish `key : ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ I ≤ t.ker`. Introduce `T t`. Establish `hW : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : T.Opens) (hW : IsAffineOpen W) (e : W ≤ t ⁻¹ᵁ U), P (Spec Γ(T, W)) (hW.fromSpec ≫ t) ↔ J U hU ≤ RingHom.ker (t.appLE U W e).hom`. Introduce `U hU W hW e`. Rewrite using `[← hJ' U hU, IsAffineOpen.SpecMap_appLE_fromSpec t hU hW e]`.

Prove the components needed by the constructor for the conclusion. Introduce `hP`. Use `Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(t.app U.1).hom a = 0`. Use `eq_zero_of_affine_restrict _ fun W hWa e => ?_` and prove the remaining obligations.

Conclude with `(hW U.1 U.2 W hWa e).1 (stab _ _ _ _ hP) ha`. Introduce `hI`. Use `loc T t fun x => ?_` and prove the remaining obligations. Take `⟨U, hU, hxU, -⟩` from `exists_isAffineOpen_mem_and_subset (U := (⊤ : Y.Opens)) (x := t x) trivial`. Take `⟨W, hWa, hxW, hWU⟩` from `exists_isAffineOpen_mem_and_subset (U := t ⁻¹ᵁ U) (x := x) hxU`.

Establish `e : W ≤ t ⁻¹ᵁ U` using `hWU`. Establish `hk : J U hU ≤ RingHom.ker (t.appLE U W e).hom` using `fun a ha => by`. Establish `h0 : (t.app U).hom a = 0` using `t.ideal_ker_le ⟨U, hU⟩ (hI ⟨U, hU⟩ ha)`. Express the relevant statement in the definitionally equal form `(T.presheaf.map (homOfLE e).op).hom ((t.app U).hom a) = 0`. Rewrite using `[h0, map_zero]`.

Establish `hp` using `stab _ _ hWa.isoSpec.hom _ ((hW U hU W hWa e).2 hk)`. Establish `e2 : hWa.isoSpec.hom ≫ hWa.fromSpec = W.ι`. Rewrite using `[IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc]`. Rewrite `hp` using `[← Category.assoc, e2]`. Conclude with `⟨W, hxW, hp⟩`.

Use `⟨I.subscheme, I.subschemeι, inferInstance, fun T t => (key T t).trans ⟨fun h => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨IsClosedImmersion.lift I.subschemeι t (by rwa [I.ker_subschemeι]), IsClosedImmersion.lift_fac _ _ _⟩`. Introduce and unpack `⟨z, rfl⟩`. Conclude with `I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)`.
-/
theorem exists_closed_subscheme (Y : Scheme.{0}) (P : ∀ T : Scheme.{0}, (T ⟶ Y) → Prop)
    (stab : ∀ (T T' : Scheme.{0}) (h : T' ⟶ T) (t : T ⟶ Y), P T t → P T' (h ≫ t))
    (loc : ∀ (T : Scheme.{0}) (t : T ⟶ Y),
      (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ P W.toScheme (W.ι ≫ t)) → P T t)
    (rep : ∀ (U : Y.Opens) (hU : IsAffineOpen U), ∃ J : Ideal Γ(Y, U),
      ∀ (R' : Type) [CommRing R'] (g : Γ(Y, U) →+* R'),
      (P (Spec (CommRingCat.of R')) (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) ↔
        J ≤ RingHom.ker g)) :
    ∃ (Z : Scheme.{0}) (i : Z ⟶ Y), IsClosedImmersion i ∧
      ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  choose J hJ using rep
  have hJ' : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (R : CommRingCat.{0}) (g : Γ(Y, U) ⟶ R),
      P (Spec R) (Spec.map g ≫ hU.fromSpec) ↔ J U hU ≤ RingHom.ker g.hom :=
    fun U hU R g => hJ U hU R g.hom
  let I : Y.IdealSheafData :=
    { ideal := fun U => J U.1 U.2
      map_ideal_basicOpen := by
        intro U f
        refine ideal_eq_of_le_ker_iff fun R _ g => ?_
        rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
        refine (hJ U.1 U.2 R _).symm.trans (Iff.trans ?_ (hJ _ (Y.affineBasicOpen f).2 R g))
        have e := U.2.map_fromSpec (Y.affineBasicOpen f).2 (homOfLE (Y.basicOpen_le f)).op
        rw [← e, ← Category.assoc, ← Spec.map_comp]
        rfl }
  have key : ∀ (T : Scheme.{0}) (t : T ⟶ Y), P T t ↔ I ≤ t.ker := by
    intro T t
    have hW : ∀ (U : Y.Opens) (hU : IsAffineOpen U) (W : T.Opens) (hW : IsAffineOpen W)
        (e : W ≤ t ⁻¹ᵁ U), P (Spec Γ(T, W)) (hW.fromSpec ≫ t) ↔
          J U hU ≤ RingHom.ker (t.appLE U W e).hom := by
      intro U hU W hW e
      rw [← hJ' U hU, IsAffineOpen.SpecMap_appLE_fromSpec t hU hW e]
    constructor
    · intro hP
      refine Scheme.IdealSheafData.le_ofIdeals_iff.2 fun U a ha => ?_
      change (t.app U.1).hom a = 0
      refine eq_zero_of_affine_restrict _ fun W hWa e => ?_
      exact (hW U.1 U.2 W hWa e).1 (stab _ _ _ _ hP) ha
    · intro hI
      refine loc T t fun x => ?_
      obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset
        (U := (⊤ : Y.Opens)) (x := t x) trivial
      obtain ⟨W, hWa, hxW, hWU⟩ := exists_isAffineOpen_mem_and_subset
        (U := t ⁻¹ᵁ U) (x := x) hxU
      have e : W ≤ t ⁻¹ᵁ U := hWU
      have hk : J U hU ≤ RingHom.ker (t.appLE U W e).hom := fun a ha => by
        have h0 : (t.app U).hom a = 0 := t.ideal_ker_le ⟨U, hU⟩ (hI ⟨U, hU⟩ ha)
        change (T.presheaf.map (homOfLE e).op).hom ((t.app U).hom a) = 0
        rw [h0, map_zero]
      have hp := stab _ _ hWa.isoSpec.hom _ ((hW U hU W hWa e).2 hk)
      have e2 : hWa.isoSpec.hom ≫ hWa.fromSpec = W.ι := by
        rw [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc]
      rw [← Category.assoc, e2] at hp
      exact ⟨W, hxW, hp⟩
  refine ⟨I.subscheme, I.subschemeι, inferInstance, fun T t => (key T t).trans ⟨fun h => ?_, ?_⟩⟩
  · exact ⟨IsClosedImmersion.lift I.subschemeι t (by rwa [I.ker_subschemeι]),
      IsClosedImmersion.lift_fac _ _ _⟩
  · rintro ⟨z, rfl⟩
    exact I.ker_subschemeι.ge.trans (Scheme.Hom.le_ker_comp _ _)

end GlobalTheory.CompanionTheory.TrivLoc.Glue
