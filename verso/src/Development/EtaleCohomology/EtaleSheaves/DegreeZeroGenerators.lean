import Development.EtaleCohomology.EtaleSheaves.ZeroSheafMaps.EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerat

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace LateralTheory.E.DegreeZeroGenerators
open LateralTheory.E.EtaleTopologySheaves LateralTheory.E.LeafDegCut LateralTheory.E.LeafShMapZeroPf LateralTheory.E.LeafShMapZeroPf.Gen

abbrev Rq (q : ℕ) := ULift.{1} (ZMod q)

abbrev Gq (q : ℕ) : Type 0 ⥤ ModuleCat.{1} (Rq q) := uliftFunctor.{1, 0} ⋙ ModuleCat.free (Rq q)

abbrev P0 (B : Scheme.{0}) (q : ℕ) (U : B.Etale) : B.Etaleᵒᵖ ⥤ ModuleCat.{1} (Rq q) :=
  ((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).obj (yoneda.obj U)

def gen {B : Scheme.{0}} {q : ℕ} (U : B.Etale) : ((F0 B q).obj U).obj.obj (op U) :=
  (toSheafify (EtTop B) (P0 B q U)).app (op U) (ModuleCat.freeMk (ULift.up (𝟙 U)))

/- English proof (translation)
Establish `h1` using `ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality (EtTop B) (((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).map (yoneda.map a))) (op U')) (ModuleCat.freeMk (ULift.up (𝟙 U')))`. Establish `h2` using `ConcreteCategory.congr_hom ((toSheafify (EtTop B) (P0 B q U)).naturality a.op) (ModuleCat.freeMk (ULift.up (𝟙 U)))`. Simplify using `only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1 h2`. Unfold `gen`. Use `Eq.trans ?_ (h1.symm.trans ?_)` and prove the remaining obligations.

Both sides reduce to the same expression. Use `Eq.trans ?_ h2` and prove the remaining obligations. Use `congr 1`. Simplify using `only [Gq, Functor.comp_map]`. Use `erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]`.

Use `show ModuleCat.freeMk (ULift.up (𝟙 U' ≫ a)) = ModuleCat.freeMk (ULift.up (a ≫ 𝟙 U))`. Simplify using the standard rewrite rules.
-/
theorem gen_nat {B : Scheme.{0}} {q : ℕ} {U U' : B.Etale} (a : U' ⟶ U) :
    ((F0 B q).map a).hom.app (op U') (gen U') = ((F0 B q).obj U).obj.map a.op (gen U) := by
  have h1 := ConcreteCategory.congr_hom (NatTrans.congr_app (toSheafify_naturality (EtTop B)
    (((Functor.whiskeringRight B.Etaleᵒᵖ (Type 0) (ModuleCat.{1} (Rq q))).obj (Gq q)).map (yoneda.map a))) (op U'))
    (ModuleCat.freeMk (ULift.up (𝟙 U')))
  have h2 := ConcreteCategory.congr_hom ((toSheafify (EtTop B) (P0 B q U)).naturality a.op)
    (ModuleCat.freeMk (ULift.up (𝟙 U)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at h1 h2
  unfold gen
  refine Eq.trans ?_ (h1.symm.trans ?_)
  · rfl
  · refine Eq.trans ?_ h2
    congr 1
    simp only [Gq, Functor.comp_map]
    erw [ModuleCat.free_map_apply, ModuleCat.free_map_apply]
    show ModuleCat.freeMk (ULift.up (𝟙 U' ≫ a)) = ModuleCat.freeMk (ULift.up (a ≫ 𝟙 U))
    simp

/- English proof (translation)
Set `φ : P0 B q U ⟶ H.obj` to `{ app := fun W => ModuleCat.freeDesc (TypeCat.ofHom (fun f : ULift.{1} (W.unop ⟶ U) => H.obj.map f.down.op x)) naturality := by`. Introduce `W W' f`. Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce `y`. Simplify using `only [Gq, ConcreteCategory.comp_apply, Functor.comp_map]`.

Use `erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]`. Use `show H.obj.map (f.unop ≫ y.down).op x = H.obj.map f (H.obj.map y.down.op x)`. Simplify using `}`. Use `⟨((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).symm φ, ?_⟩` and prove the remaining obligations. Establish `e` using `((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).apply_symm_apply φ`.

Rewrite `e` using `[Adjunction.homEquiv_unit]`. Establish `e2` using `ConcreteCategory.congr_hom (NatTrans.congr_app e (op U)) (ModuleCat.freeMk (ULift.up (𝟙 U)))`. Simplify using `only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e2`. Unfold `gen`. Use `Eq.trans ?_ (e2.trans ?_)` and prove the remaining obligations.

Both sides reduce to the same expression. Simplify using `only [φ] erw [ModuleCat.freeDesc_apply] show H.obj.map (𝟙 U).op x = x`. Simplify using the standard rewrite rules.
-/
theorem free_etale_sheaf_zmod_exists_hom_sending_generator {B : Scheme.{0}} {q : ℕ} (H : SShv B q) (U : B.Etale) (x : H.obj.obj (op U)) :
    ∃ t : (F0 B q).obj U ⟶ H, t.hom.app (op U) (gen U) = x := by
  let φ : P0 B q U ⟶ H.obj :=
    { app := fun W => ModuleCat.freeDesc (TypeCat.ofHom (fun f : ULift.{1} (W.unop ⟶ U) => H.obj.map f.down.op x))
      naturality := by
        intro W W' f
        apply ModuleCat.free_hom_ext
        intro y
        simp only [Gq, ConcreteCategory.comp_apply, Functor.comp_map]
        erw [ModuleCat.free_map_apply, ModuleCat.freeDesc_apply, ModuleCat.freeDesc_apply]
        show H.obj.map (f.unop ≫ y.down).op x = H.obj.map f (H.obj.map y.down.op x)
        simp }
  refine ⟨((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).symm φ, ?_⟩
  have e := ((sheafificationAdjunction (EtTop B) _).homEquiv (P0 B q U) H).apply_symm_apply φ
  rw [Adjunction.homEquiv_unit] at e
  have e2 := ConcreteCategory.congr_hom (NatTrans.congr_app e (op U)) (ModuleCat.freeMk (ULift.up (𝟙 U)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at e2
  unfold gen
  refine Eq.trans ?_ (e2.trans ?_)
  · rfl
  · simp only [φ]
    erw [ModuleCat.freeDesc_apply]
    show H.obj.map (𝟙 U).op x = x
    simp

/- English proof (translation)
Introduce `B q H H' g h`. Apply `(sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map_injective` to reduce the goal to its premises. Rewrite using `[Functor.map_zero]`. Apply `NatTrans.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `U`.

Proceed by induction on `U with | op U => ?_`. Apply `ModuleCat.hom_ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Take `⟨t, ht⟩` from `free_etale_sheaf_zmod_exists_hom_sending_generator H U x`.

Take `⟨S, hS, hP⟩` from `h U t`. Establish `key : ∀ (U' : B.Etale) (a : U' ⟶ U), S a → H'.obj.map a.op (g.hom.app (op U) x) = H'.obj.map a.op 0`. Introduce `U' a ha`. Establish `h3` using `congrArg (fun m : (F0 B q).obj U' ⟶ H' => ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map m).app (op U') (gen U')) (hP U' a ha)`. Simplify using `only [Functor.map_comp, Functor.map_zero, NatTrans.comp_app, NatTrans.app_zero, ConcreteCategory.comp_apply] at h3`.

Rewrite using `[map_zero, ← ht]`. Establish `n` using `ConcreteCategory.congr_hom (g.hom.naturality a.op) (t.hom.app (op U) (gen U))`. Simplify using `only [ConcreteCategory.comp_apply] at n`. Rewrite using `[← n]`. Establish `n2` using `ConcreteCategory.congr_hom (t.hom.naturality a.op) (gen U)`.

Simplify using `only [ConcreteCategory.comp_apply] at n2`. Rewrite using `[← n2, ← gen_nat a]`. Conclude with `h3`. Use `Sheaf.isSeparated H' U S hS _ 0 key` as an intermediate fact. Simplify using `only [NatTrans.app_zero]`.

Conclude with `this`.
-/
theorem free_etale_sheaf_zmod_representable_generates : EtaleSheafMapZeroOfLocallyZeroOnFreeSheafGenerators := by
  intro B q H H' g h
  apply (sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map_injective
  rw [Functor.map_zero]
  apply NatTrans.ext
  funext U
  induction U with | op U => ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  obtain ⟨t, ht⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator H U x
  obtain ⟨S, hS, hP⟩ := h U t
  have key : ∀ (U' : B.Etale) (a : U' ⟶ U), S a →
      H'.obj.map a.op (g.hom.app (op U) x) = H'.obj.map a.op 0 := by
    intro U' a ha
    have h3 := congrArg (fun m : (F0 B q).obj U' ⟶ H' =>
      ((sheafToPresheaf (EtTop B) (ModuleCat.{1} (Rq q))).map m).app (op U') (gen U')) (hP U' a ha)
    simp only [Functor.map_comp, Functor.map_zero, NatTrans.comp_app, NatTrans.app_zero,
      ConcreteCategory.comp_apply] at h3
    rw [map_zero, ← ht]
    have n := ConcreteCategory.congr_hom (g.hom.naturality a.op) (t.hom.app (op U) (gen U))
    simp only [ConcreteCategory.comp_apply] at n
    rw [← n]
    have n2 := ConcreteCategory.congr_hom (t.hom.naturality a.op) (gen U)
    simp only [ConcreteCategory.comp_apply] at n2
    rw [← n2, ← gen_nat a]
    exact h3
  have := Sheaf.isSeparated H' U S hS _ 0 key
  simp only [NatTrans.app_zero]
  exact this

end LateralTheory.E.DegreeZeroGenerators
