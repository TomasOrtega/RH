import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
A polynomial algebra on finitely many variables is finitely presented by those generators with no relations. It is formally smooth because lifts of the finitely many variable images across a nilpotent extension define a lift of the entire polynomial map. Together these give smoothness.
-/
private theorem algebra_smooth_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    Algebra.Smooth k (MvPolynomial (ULift.{u} (Fin n)) k) :=
  ⟨inferInstance, inferInstance⟩

/- English proof (authored)
The constant-coefficient inclusion defines the polynomial algebra structure. Smoothness of this algebra is equivalent to smoothness of that ring homomorphism.
-/
private theorem ringHom_smooth_algebraMap_mvPolynomial (k : Type u) [Field k] (n : ℕ) :
    RingHom.Smooth (algebraMap k (MvPolynomial (ULift.{u} (Fin n)) k)) :=
  RingHom.smooth_algebraMap.mpr (algebra_smooth_mvPolynomial k n)

/- English proof (authored)
The standard isomorphism between affine space and the spectrum of its polynomial ring is an isomorphism over the ground field. Its inverse commutes with the structure maps, with the spectrum structure map induced by the constant-coefficient inclusion.
-/
private theorem specIso_inv_comp_affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : ℕ) :
    (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).inv ≫
        affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      Spec.map (CommRingCat.ofHom
        (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) :=
  AffineSpace.SpecIso_inv_over _

/- English proof (authored)
Apply the compatibility of the inverse affine-space isomorphism with the structure maps and precompose with the forward isomorphism. The two isomorphisms cancel, giving the stated expression.
-/
private theorem affineSpaceIndexedByToSpec_eq (k : Type u) [Field k] (n : ℕ) :
    affineSpaceIndexedByToSpec k (ULift.{u} (Fin n)) =
      (AffineSpace.SpecIso (ULift.{u} (Fin n)) (CommRingCat.of k)).hom ≫
        Spec.map (CommRingCat.ofHom
          (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin n)) k)) := by
  rw [← specIso_inv_comp_affineSpaceIndexedByToSpec k n, Iso.hom_inv_id_assoc]

/- English proof (authored)
The map from the polynomial spectrum to the field spectrum is smooth because the corresponding algebra map is smooth. The affine-space structural map is obtained from it by precomposing with an isomorphism, so it is smooth.
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

/- English proof (authored)
Use the whole affine space as a coordinate neighborhood at every point, with its identity chart and all coordinates available. This chart is étale. The boundary list is empty, so the conditions assigning coordinate hyperplanes to boundary members and requiring distinct coordinates hold vacuously.
-/
theorem nilIsStrictNormalCrossingsOnAffineSpace : NilIsStrictNormalCrossingsOnAffineSpace.{u} := by
  intro k _ n
  refine ⟨by simp, fun x => ⟨⊤, trivial, n,
    ⟨(⊤ : (affineSpaceIndexedBy k (ULift.{u} (Fin n))).Opens).ι, rfl, ?_⟩,
    fun _ => none, by simp, by simp, by simp⟩⟩
  infer_instance

end FunctorialResolution.EmbeddedResolution
