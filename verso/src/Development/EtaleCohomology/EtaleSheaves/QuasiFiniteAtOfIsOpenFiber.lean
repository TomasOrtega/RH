import Development.EtaleCohomology.EtaleSheaves.LeafSpreadLQFMapVtuPfG

noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace LateralTheory.E.QuasiFiniteAtDescent

/- English proof (translation)
Establish `hy : y = f a`. Rewrite using `[← hza, ← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply]`. Simplify using the standard rewrite rules. Substitute `hy` using the available equality. Establish `: z = f.asFiber a`.

Apply `(f.fiberι (f a)).isEmbedding.injective` to reduce the goal to its premises. Rewrite using `[hza, Scheme.Hom.fiberι_asFiber]`. Rewrite using `[Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← this]`. Conclude with `hz`.
-/
theorem quasiFiniteAt_of_isOpen_fiber {X Y : Scheme.{0}} (f : X ⟶ Y) [LocallyOfFiniteType f]
    (y : Y) (z : f.fiber y) (a : X) (hza : f.fiberι y z = a) (hz : IsOpen ({z} : Set (f.fiber y))) :
    f.QuasiFiniteAt a := by
  have hy : y = f a := by
    rw [← hza, ← Scheme.Hom.comp_apply, Scheme.Hom.fiber_fac, Scheme.Hom.comp_apply]
    simp
  subst hy
  have : z = f.asFiber a := by
    apply (f.fiberι (f a)).isEmbedding.injective
    rw [hza, Scheme.Hom.fiberι_asFiber]
  rw [Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber, ← this]
  exact hz

/- English proof (translation)
Establish `hx' : IsOpen ({γ.asFiber x} : Set (γ.fiber (γ x)))` using `Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx`. Establish `hopen` using `φ.isOpenMap _ hx'`. Establish `h2 : IsOpen ({φ (γ.asFiber x)} : Set (g.fiber (vB (γ x))))`. Use `hopen using 1` and compare the differences between its conclusion and the goal. Conclude with `(Set.image_singleton).symm`.

Use `quasiFiniteAt_of_isOpen_fiber g (vB (γ x)) (φ (γ.asFiber x)) (vA x) ?_ h2` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]`.
-/
theorem qf_of_fiberMap {CA CB A B : Scheme.{0}} (γ : CA ⟶ CB) (g : A ⟶ B) (vA : CA ⟶ A) (vB : CB ⟶ B)
    [LocallyOfFiniteType g] [LocallyOfFiniteType γ] (x : CA)
    (φ : γ.fiber (γ x) ⟶ g.fiber (vB (γ x))) (hφ : UniversallyOpen φ)
    (e : φ ≫ g.fiberι (vB (γ x)) = γ.fiberι (γ x) ≫ vA) (hx : γ.QuasiFiniteAt x) :
    g.QuasiFiniteAt (vA x) := by
  have hx' : IsOpen ({γ.asFiber x} : Set (γ.fiber (γ x))) :=
    Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hx
  have hopen := φ.isOpenMap _ hx'
  have h2 : IsOpen ({φ (γ.asFiber x)} : Set (g.fiber (vB (γ x)))) := by
    convert hopen using 1
    exact (Set.image_singleton).symm
  refine quasiFiniteAt_of_isOpen_fiber g (vB (γ x)) (φ (γ.asFiber x)) (vA x) ?_ h2
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply, Scheme.Hom.fiberι_asFiber]

/- English proof (translation)
Introduce `CA CB A B γ g vA vB sq hg x hx`. Establish `: LocallyOfFiniteType γ` using `MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq hg`. Establish `sqF` using `isPullback_fiberToSpecResidueField_of_isPullback sq (γ x)`. Establish `hφ` using `MorphismProperty.of_isPullback (P := @UniversallyOpen) sqF.flip inferInstance`. Use `qf_of_fiberMap γ g vA vB x _ hφ ?_ hx` and prove the remaining obligations.

Conclude with `pullback.lift_fst _ _ _`.
-/
theorem LeafQFAtDescend_of : LateralTheory.E.SpreadingOutLocallyQuasiFinite.LeafQFAtDescend := by
  intro CA CB A B γ g vA vB sq hg x hx
  have : LocallyOfFiniteType γ :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) sq hg
  have sqF := isPullback_fiberToSpecResidueField_of_isPullback sq (γ x)
  have hφ := MorphismProperty.of_isPullback (P := @UniversallyOpen) sqF.flip inferInstance
  refine qf_of_fiberMap γ g vA vB x _ hφ ?_ hx
  exact pullback.lift_fst _ _ _

end LateralTheory.E.QuasiFiniteAtDescent
