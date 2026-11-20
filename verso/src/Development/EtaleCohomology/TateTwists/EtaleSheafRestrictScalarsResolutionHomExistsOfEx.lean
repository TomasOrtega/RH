import Development.EtaleCohomology.TateTwists.EtaleSheafRestrictScalarsInjectiveResolutionHomE
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import Mathlib.CategoryTheory.Triangulated.Orthogonal
import Mathlib.Algebra.Homology.Localization
import Mathlib.CategoryTheory.Abelian.Injective.Extend

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

/- English proof (translation)
Establish `hL` using `CochainComplex.IsKInjective.rightOrthogonal L`. Rewrite `hL` using `[← ObjectProperty.isLocal_trW]`. Establish `hs : (HomotopyCategory.subcategoryAcyclic C).trW ((HomotopyCategory.quotient C _).map s)`. Rewrite using `[← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.quotient_map_mem_quasiIso_iff]`. Conclude with `(HomologicalComplex.mem_quasiIso_iff _).2 inferInstance`.

Take `⟨g', hg'⟩` from `(hL _ hs).2 ((HomotopyCategory.quotient C _).map f)`. Take `⟨g, rfl⟩` from `(HomotopyCategory.quotient C _).map_surjective g'`. Use `⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩` and prove the remaining obligations. Simplify using `using hg'`.
-/
lemma restr_ex_hom_ext_of_qis {C : Type*} [Category C] [Abelian C] {K K' L : CochainComplex C ℤ}
    [L.IsKInjective] (s : K ⟶ K') [QuasiIso s] (f : K ⟶ L) :
    ∃ g : K' ⟶ L, Nonempty (Homotopy (s ≫ g) f) := by
  have hL := CochainComplex.IsKInjective.rightOrthogonal L
  rw [← ObjectProperty.isLocal_trW] at hL
  have hs : (HomotopyCategory.subcategoryAcyclic C).trW ((HomotopyCategory.quotient C _).map s) := by
    rw [← HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact (HomologicalComplex.mem_quasiIso_iff _).2 inferInstance
  obtain ⟨g', hg'⟩ := (hL _ hs).2 ((HomotopyCategory.quotient C _).map f)
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C _).map_surjective g'
  refine ⟨g, ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  simpa using hg'

def EtaleSheafRestrictScalarsFunctorExact : Prop :=
  ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S),
    PreservesFiniteLimits (restr φ) ∧ PreservesFiniteColimits (restr φ)

/- English proof (translation)
Introduce `R S _ _ φ F`. Take `⟨h1, h2⟩` from `hE R S φ`. Set `G` to `restr φ`. Establish `: G.Additive` using `G.additive_of_preserves_binary_products`. Set `IS` to `injectiveResolution F`.

Set `IR` to `injectiveResolution (G.obj F)`. Establish `: (res R (G.obj F)).IsKInjective` using `inferInstanceAs IR.cochainComplex.IsKInjective`. Establish `: (res R (G.obj F)).IsStrictlyGE 0` using `inferInstanceAs (IR.cochainComplex.IsStrictlyGE 0)`. Set `s` to `(G.mapHomologicalComplex (ComplexShape.up ℤ)).map IS.ι'`. Establish `: QuasiIso s` using `inferInstance`.

Set `f0` to `(HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F ≫ IR.ι'`. Take `⟨g, ⟨h⟩⟩` from `restr_ex_hom_ext_of_qis (L := res R (G.obj F)) s f0`. Use `⟨fun n => g.f n, fun i j => (g.comm i j).symm, ?_⟩` and prove the remaining obligations. Establish `hz1 : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X 1)` using `G.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by decide))`. Establish `key : (s ≫ g).f 0 = f0.f 0`.

Rewrite using `[h.comm 0]`. Establish `e1 : dNext 0 h.hom = 0`. Establish `e : h.hom 1 0 = 0` using `hz1.eq_of_src _ _`. Rewrite using `[dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl), e, comp_zero]`. Establish `e2 : prevD 0 h.hom = 0`.

Rewrite using `[prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl), ((res R (G.obj F)).isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_of_tgt (h.hom 0 (-1)) 0, zero_comp]`. Rewrite using `[e1, e2, zero_add, zero_add]`. Establish `key2` using `congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) key`. Simplify using `only [s, f0, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f, HomologicalComplex.singleMapHomologicalComplex_hom_app_self, ← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, Category.id_comp] at key2`. Establish `key3 : G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ G.map (IS.ι'.f 0) ≫ g.f 0 = (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv ≫ IR.ι'.f 0`.

Use `key2.trans ?_` and prove the remaining obligations. Establish `c2 : ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F).f 0 = G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv` using `HomologicalComplex.singleMapHomologicalComplex_hom_app_self _ _ _ _`. Combine the equalities or inequalities in the displayed calculation. Conclude with `congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) (congrArg (fun y => y ≫ IR.ι'.f 0) c2)`. Use `_ = _ := by`.

Establish `aux : ∀ {A B : Shv S} {Y Z : Shv R} (e : A ≅ B) (u : G.obj B ⟶ Y) (v : Y ⟶ Z), G.map e.inv ≫ (G.map e.hom ≫ u) ≫ v = u ≫ v`. Introduce `A B Y Z e u v`. Rewrite using `[← Category.assoc, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]`. Conclude with `aux _ _ _`. Simplify using `only [resι]`.

Use `erw [Functor.map_comp, Category.assoc]`. Conclude with `key3`.
-/
theorem etaleSheaf_restrictScalars_resolution_hom_exists_of_exact (hE : EtaleSheafRestrictScalarsFunctorExact) : EtaleSheafRestrictScalarsInjectiveResolutionHomExists := by
  intro R S _ _ φ F
  obtain ⟨h1, h2⟩ := hE R S φ
  let G := restr φ
  have : G.Additive := G.additive_of_preserves_binary_products
  let IS := injectiveResolution F
  let IR := injectiveResolution (G.obj F)
  have : (res R (G.obj F)).IsKInjective := inferInstanceAs IR.cochainComplex.IsKInjective
  have : (res R (G.obj F)).IsStrictlyGE 0 := inferInstanceAs (IR.cochainComplex.IsStrictlyGE 0)
  let s := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map IS.ι'
  have : QuasiIso s := inferInstance
  let f0 := (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F ≫ IR.ι'
  obtain ⟨g, ⟨h⟩⟩ := restr_ex_hom_ext_of_qis (L := res R (G.obj F)) s f0
  refine ⟨fun n => g.f n, fun i j => (g.comm i j).symm, ?_⟩
  have hz1 : IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X 1) :=
    G.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F 1 (by decide))
  have key : (s ≫ g).f 0 = f0.f 0 := by
    rw [h.comm 0]
    have e1 : dNext 0 h.hom = 0 := by
      have e : h.hom 1 0 = 0 := hz1.eq_of_src _ _
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl), e, comp_zero]
    have e2 : prevD 0 h.hom = 0 := by
      rw [prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 from rfl),
        ((res R (G.obj F)).isZero_of_isStrictlyGE 0 (-1) (by decide)).eq_of_tgt (h.hom 0 (-1)) 0, zero_comp]
    rw [e1, e2, zero_add, zero_add]
  have key2 := congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) key
  simp only [s, f0, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, ← Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Functor.map_id, Category.id_comp] at key2
  have key3 : G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ G.map (IS.ι'.f 0) ≫ g.f 0 =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv ≫ IR.ι'.f 0 := by
    refine key2.trans ?_
    have c2 : ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F).f 0 =
        G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv :=
      HomologicalComplex.singleMapHomologicalComplex_hom_app_self _ _ _ _
    calc _ = G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ ((G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).hom ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 (G.obj F)).inv) ≫ IR.ι'.f 0) := by
          exact congrArg (fun x => G.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv ≫ x) (congrArg (fun y => y ≫ IR.ι'.f 0) c2)
      _ = _ := by
          have aux : ∀ {A B : Shv S} {Y Z : Shv R} (e : A ≅ B) (u : G.obj B ⟶ Y) (v : Y ⟶ Z),
              G.map e.inv ≫ (G.map e.hom ≫ u) ≫ v = u ≫ v := by
            intro A B Y Z e u v
            rw [← Category.assoc, ← Category.assoc, ← G.map_comp, Iso.inv_hom_id, G.map_id, Category.id_comp]
          exact aux _ _ _
  simp only [resι]
  erw [Functor.map_comp, Category.assoc]
  exact key3

end LateralTheory.EtaleFoundations
