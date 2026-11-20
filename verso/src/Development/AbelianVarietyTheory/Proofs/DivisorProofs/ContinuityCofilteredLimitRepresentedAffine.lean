import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousCofilteredAffineLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfEtaleCohomologyEquivalenceDiagramStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

/- English proof (translation)
Introduce `n`. Use `Function.bijective_iff_has_inverse.mpr ⟨pull R f.inv F n, fun x => ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[← pull_comp, Iso.inv_hom_id, pull_id]`. Rewrite using `[← pull_comp, Iso.hom_inv_id, pull_id]`.
-/
theorem eqv_of_iso (R : Type) [CommRing R] (F : Shv R) {E E' : Spc} (f : E ≅ E') : Eqv R f.hom F := by
  intro n
  refine Function.bijective_iff_has_inverse.mpr ⟨pull R f.inv F n, fun x => ?_, fun y => ?_⟩
  · rw [← pull_comp, Iso.inv_hom_id, pull_id]
  · rw [← pull_comp, Iso.hom_inv_id, pull_id]

/- English proof (translation)
Introduce `R _ F hF I _ _ D c hc hD hpt`. Use `choose Z hZ he using hD`. Take `⟨Z0, ⟨e0⟩⟩` from `hpt`. Set `e : ∀ i, yoneda.obj (Z i) ≅ D.obj i` to `fun i => (he i).some`. Set `G : I ⥤ Scheme.{0}` to `{ obj := Z map := fun {i j} f => yoneda.preimage ((e i).hom ≫ D.map f ≫ (e j).inv) map_id := fun i => yoneda.map_injective (by simp) map_comp := fun {i j k} f g => yoneda.map_injective (by simp) }`.

Set `isoYD : G ⋙ yoneda ≅ D` to `NatIso.ofComponents e (fun {i j} f => by simp [G])`. Set `s : Cone G` to `{ pt := Z0 π := { app := fun i => yoneda.preimage (e0.hom ≫ c.π.app i ≫ (e i).inv) naturality := fun i j f => yoneda.map_injective (by simp [G]) } }`. Establish `hs : IsLimit s`. Apply `isLimitOfReflects yoneda` to reduce the goal to its premises. Establish `h1 : IsLimit ((Cone.postcompose isoYD.inv).obj c)` using `(IsLimit.postcomposeInvEquiv isoYD c).symm hc`.

Use `h1.ofIsoLimit (Cone.ext e0.symm (fun i => ?_))` and prove the remaining obligations. Simplify using `[s]`. Both sides reduce to the same expression. Establish `h0 : ContCone R F (sch.mapCone s)` using `GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I G s hs hZ`. Set `αI : G ⋙ sch ≅ D ⋙ disc` to `(Functor.associator G yoneda disc).symm ≪≫ Functor.isoWhiskerRight isoYD disc`.

Set `βI : sch.obj Z0 ≅ disc.obj c.pt` to `disc.mapIso e0`. Use `(GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F I (G ⋙ sch) (D ⋙ disc) (sch.mapCone s) (disc.mapCone c) αI.hom βI.hom (fun i => ?_) (fun i => eqv_of_iso R F (αI.app i)) (eqv_of_iso R F βI)).mp h0` and prove the remaining obligations. Simplify using `only [Functor.mapCone_π_app, αI, βI, s, sch, Functor.comp_map]`. Simplify using `[isoYD, ← Functor.map_comp]`.
-/
theorem contCone_of_represented : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (D : I ⥤ PSh) (c : Cone D), IsLimit c → (∀ i, ∃ Z : Scheme.{0}, IsAffine Z ∧ Nonempty (yoneda.obj Z ≅ D.obj i)) → (∃ Z : Scheme.{0}, Nonempty (yoneda.obj Z ≅ c.pt)) → ContCone R F (disc.mapCone c) := by
  intro R _ F hF I _ _ D c hc hD hpt
  choose Z hZ he using hD
  obtain ⟨Z0, ⟨e0⟩⟩ := hpt
  let e : ∀ i, yoneda.obj (Z i) ≅ D.obj i := fun i => (he i).some

  let G : I ⥤ Scheme.{0} :=
    { obj := Z
      map := fun {i j} f => yoneda.preimage ((e i).hom ≫ D.map f ≫ (e j).inv)
      map_id := fun i => yoneda.map_injective (by simp)
      map_comp := fun {i j k} f g => yoneda.map_injective (by simp) }
  let isoYD : G ⋙ yoneda ≅ D := NatIso.ofComponents e (fun {i j} f => by simp [G])

  let s : Cone G :=
    { pt := Z0
      π :=
        { app := fun i => yoneda.preimage (e0.hom ≫ c.π.app i ≫ (e i).inv)
          naturality := fun i j f => yoneda.map_injective (by simp [G]) } }
  have hs : IsLimit s := by
    apply isLimitOfReflects yoneda
    have h1 : IsLimit ((Cone.postcompose isoYD.inv).obj c) := (IsLimit.postcomposeInvEquiv isoYD c).symm hc
    refine h1.ofIsoLimit (Cone.ext e0.symm (fun i => ?_))
    simp [s]
    rfl
  have h0 : ContCone R F (sch.mapCone s) := GlobalTheory.T.cohomologyContinuous_cofiltered_affine_limit R F hF I G s hs hZ
  let αI : G ⋙ sch ≅ D ⋙ disc := (Functor.associator G yoneda disc).symm ≪≫ Functor.isoWhiskerRight isoYD disc
  let βI : sch.obj Z0 ≅ disc.obj c.pt := disc.mapIso e0
  refine (GlobalTheory.T.of_etaleCohomologyEquivalence_diagram R F I (G ⋙ sch) (D ⋙ disc) (sch.mapCone s) (disc.mapCone c) αI.hom βI.hom
    (fun i => ?_) (fun i => eqv_of_iso R F (αI.app i)) (eqv_of_iso R F βI)).mp h0
  simp only [Functor.mapCone_π_app, αI, βI, s, sch, Functor.comp_map]
  simp [isoYD, ← Functor.map_comp]

end GlobalTheory
