import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization.Statements
import GroundTheory.ArithmeticGeometry.SchemeCohomology.ProjectiveSpaceChart
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory GroundTheory.Arith.SchemeCoh MvPolynomial

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

/- English proof (translation)
Rewrite using `[ProjSpace.polyToChart, MvPolynomial.eval₂Hom_comp_C]`.
-/
lemma chart_structureMap_eq (A : Type u) [CommRing A] (N : ℕ) (j : Fin (N + 1)) :
    (HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading A N)
        (Submonoid.powers (X j : MvPolynomial (Fin (N + 1)) A))).comp
        (algebraMap A (ProjSpace.grading A N 0)) =
      (ProjSpace.polyToChart A j).comp C := by
  rw [ProjSpace.polyToChart, MvPolynomial.eval₂Hom_comp_C]

/- English proof (translation)
Rewrite using `[chart_structureMap_eq]`. Use `RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (ProjSpace.chartEquiv A j).symm.bijective)` and prove the remaining obligations. Rewrite using `[← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]`. Use `infer_instance`.
-/
lemma flat_chart_structureMap (A : Type u) [CommRing A] (N : ℕ) (j : Fin (N + 1)) :
    ((HomogeneousLocalization.fromZeroRingHom (ProjSpace.grading A N)
        (Submonoid.powers (X j : MvPolynomial (Fin (N + 1)) A))).comp
        (algebraMap A (ProjSpace.grading A N 0))).Flat := by
  rw [chart_structureMap_eq]
  refine RingHom.Flat.comp ?_ (RingHom.Flat.of_bijective (ProjSpace.chartEquiv A j).symm.bijective)
  rw [← MvPolynomial.algebraMap_eq, RingHom.flat_algebraMap_iff]
  infer_instance

/- English proof (translation)
Introduce `A _ N`. Express the relevant statement in the definitionally equal form `Flat (𝟙 _ ≫ ProjSpace.toSpecBase A N)`. Rewrite using `[Category.id_comp]`. Establish `: IsZariskiLocalAtSource @Flat` using `HasRingHomProperty.instIsZariskiLocalAtSource`. Use `(IsZariskiLocalAtSource.iff_of_iSup_eq_top _ (ProjSpace.iSup_stdOpen (A := A) (n := N))).mpr fun j => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Flat ((Proj.basicOpen (ProjSpace.grading A N) (X j)).ι ≫ ProjSpace.toSpecBase A N)`. Establish `e : (Proj.basicOpen (ProjSpace.grading A N) (X j)).ι = (Proj.basicOpenIsoSpec (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos).hom ≫ Proj.awayι (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos`. Rewrite using `[← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]`. Establish `h : Flat (Proj.awayι (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos ≫ ProjSpace.toSpecBase A N)`. Rewrite using `[ProjSpace.toSpecBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, Flat.SpecMap_iff]`.

Conclude with `flat_chart_structureMap A N j`. Rewrite using `[e, Category.assoc]`. Use `infer_instance`.
-/
theorem PNFlat.proof : PNFlat.Statement.{u} := by
  intro A _ N
  change Flat (𝟙 _ ≫ ProjSpace.toSpecBase A N)
  rw [Category.id_comp]
  have : IsZariskiLocalAtSource @Flat := HasRingHomProperty.instIsZariskiLocalAtSource
  refine (IsZariskiLocalAtSource.iff_of_iSup_eq_top _ (ProjSpace.iSup_stdOpen (A := A) (n := N))).mpr
    fun j => ?_
  change Flat ((Proj.basicOpen (ProjSpace.grading A N) (X j)).ι ≫ ProjSpace.toSpecBase A N)
  have e : (Proj.basicOpen (ProjSpace.grading A N) (X j)).ι =
      (Proj.basicOpenIsoSpec (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos).hom ≫
        Proj.awayι (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos := by
    rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  have h : Flat (Proj.awayι (ProjSpace.grading A N) (X j) (ProjSpace.X_mem j) one_pos ≫
      ProjSpace.toSpecBase A N) := by
    rw [ProjSpace.toSpecBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp, Flat.SpecMap_iff]
    exact flat_chart_structureMap A N j
  rw [e, Category.assoc]
  infer_instance

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
