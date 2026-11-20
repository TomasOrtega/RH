import Development.EtaleCohomology.CohomologicalPurity.LeafDictPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.KummerTheory.FlasquePf

namespace LateralTheory.CohomologicalPurity.DictPf

section
variable {R : Type} [CommRing R] {G : Shv R} {X : Scheme.{0}}

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation. Use `congrArg (fun φ => ModuleCat.Hom.hom φ (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality h.op)` as an intermediate fact. Conclude with `this`.
-/
theorem ev_res' (m : (free R).obj (yoneda.obj X) ⟶ G) {V : Scheme.{0}} (h : V ⟶ X) :
    (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h) = Sec.res h (ev m) := by
  calc (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V h)
      = (m.hom.app (op V)).hom (freeGen R (yoneda.obj X) V ((yoneda.obj X).map h.op (𝟙 X))) := by simp
    _ = (m.hom.app (op V)).hom (Sec.res h (freeGen R (yoneda.obj X) X (𝟙 X))) := by rw [freeGen_res]
    _ = Sec.res h (ev m) := by
      have := congrArg (fun φ => ModuleCat.Hom.hom φ (freeGen R (yoneda.obj X) X (𝟙 X))) (m.hom.naturality h.op)
      exact this

/- English proof (translation)
Apply `((sheafificationAdjunction _ _).homEquiv _ G).injective` to reduce the goal to its premises. Unfold `ofSec`. Rewrite using `[Equiv.apply_symm_apply]`. Apply `NatTrans.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `V`.

Apply `ModuleCat.free_hom_ext` to reduce the goal to its premises. Introduce `x`. Express the relevant statement in the definitionally equal form `(m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = _`. Rewrite using `[ev_res']`. Unfold `toG`.

Use `symm`. Express the relevant statement in the definitionally equal form `ModuleCat.freeDesc _ (ModuleCat.freeMk x) = _`. Use `(ModuleCat.freeDesc_apply _ _).trans ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem eq_ofSec (m : (free R).obj (yoneda.obj X) ⟶ G) : m = ofSec G (ev m) := by
  apply ((sheafificationAdjunction _ _).homEquiv _ G).injective
  unfold ofSec
  rw [Equiv.apply_symm_apply]
  apply NatTrans.ext
  funext V
  apply ModuleCat.free_hom_ext
  intro x
  change (m.hom.app V).hom (freeGen R (yoneda.obj X) V.unop x.down) = _
  rw [ev_res']
  unfold toG
  symm
  change ModuleCat.freeDesc _ (ModuleCat.freeMk x) = _
  refine (ModuleCat.freeDesc_apply _ _).trans ?_
  rfl

end

/- English proof (translation)
Introduce `R _ G X`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `m m' h`. Rewrite using `[eq_ofSec m, eq_ofSec m', h]`. Introduce `m m'`.

Both sides reduce to the same expression. Introduce `Y f m`. Express the relevant statement in the definitionally equal form `(m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _`. Rewrite using `[freeGen_map]`. Simplify using `only [yoneda_map_app]`.

Conclude with `ev_res' m f`.
-/
theorem LeafEv_of : LeafEv := by
  intro R _ G X
  refine ⟨?_, ?_, ?_⟩
  · intro m m' h
    rw [eq_ofSec m, eq_ofSec m', h]
  · intro m m'
    rfl
  · intro Y f m
    change (m.hom.app (op Y)).hom ((((free R).map (yoneda.map f)).hom.app (op Y)).hom
      (freeGen R (yoneda.obj Y) Y (𝟙 Y))) = _
    rw [freeGen_map]
    simp only [yoneda_map_app]
    exact ev_res' m f

end LateralTheory.CohomologicalPurity.DictPf
