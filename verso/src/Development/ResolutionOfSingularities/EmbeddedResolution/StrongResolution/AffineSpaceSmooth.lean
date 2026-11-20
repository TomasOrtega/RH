import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Assemble the required witnesses or components as `⟨inferInstance, inferInstance⟩`.
-/
private theorem algebra_smooth_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    Algebra.Smooth k (MvPolynomial (ULift.{u} (Fin n)) k) :=
  ⟨inferInstance, inferInstance⟩

/- English proof (translation)
The claim follows from `RingHom.smooth_algebraMap.mpr (algebra_smooth_mvPolynomial k n)`.
-/
private theorem ringHom_smooth_algebraMap_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    RingHom.Smooth (algebraMap k (MvPolynomial (ULift.{u} (Fin n)) k)) :=
  RingHom.smooth_algebraMap.mpr (algebra_smooth_mvPolynomial k n)

/- English proof (translation)
The claim follows from `AffineSpace.SpecIso_inv_over _`.
-/
private theorem specIso_inv_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : ℕ) :
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) :=
  AffineSpace.SpecIso_inv_over _

/- English proof (translation)
Rewrite using `[← specIso_inv_comp_affineSpaceIndexedByToSpec k n, Iso.hom_inv_id_assoc]`.
-/
private theorem affineSpaceIndexedByToSpec_eq (k : Type u) [Field k] (n : ℕ) :
    affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) := by
  rw [← specIso_inv_comp_affineSpaceIndexedByToSpec k n, Iso.hom_inv_id_assoc]

/- English proof (translation)
Introduce `k _ n`. Establish `hC : AlgebraicGeometry.Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)))` using `(AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.Smooth)).mpr (ringHom_smooth_algebraMap_mvPolynomial k n)`. Rewrite using `[affineSpaceIndexedByToSpec_eq k n]`. Use `infer_instance`.
-/
theorem affineSpaceIsSmooth : AffineSpaceIsSmooth.{u} := by
  intro k _ n
  have hC : AlgebraicGeometry.Smooth
      (Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k))) :=
    (AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.Smooth)).mpr (ringHom_smooth_algebraMap_mvPolynomial k n)
  rw [affineSpaceIndexedByToSpec_eq k n]
  infer_instance

/- English proof (translation)
Introduce `k _ n`. Use `⟨by simp, fun x => ⟨⊤, trivial, n, ⟨(⊤ : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens).ι, rfl, ?_⟩, fun _ => none, by simp, by simp, by simp⟩⟩` and prove the remaining obligations. Use `infer_instance`.
-/
theorem nilIsStrictNormalCrossingsOnAffineSpace : NilIsStrictNormalCrossingsOnAffineSpace.{u} := by
  intro k _ n
  refine ⟨by simp, fun x => ⟨⊤, trivial, n,
    ⟨(⊤ : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens).ι, rfl, ?_⟩,
    fun _ => none, by simp, by simp, by simp⟩⟩
  infer_instance

end FunctorialResolution.EmbeddedResolution
