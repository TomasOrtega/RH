import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCoordinateCodimensionPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceOrigin
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.EmbeddedResolutionRule
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.ClosedEmbeddingIntoAffineSpace
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineSpaceLinearEmbeddings
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The composite preserves the structural map to the base. On each coordinate, its pullback reindexes first by the bijection and then by its inverse, so the coordinate returns to itself. These data determine the identity map of the affine space.
-/
private theorem affineSpace_reindex_symm_comp_reindex {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace.reindex (e.symm : m → n) S ≫ AffineSpace.reindex (e : n → m) S =
      𝟙 (AffineSpace n S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

/- English proof (authored)
The composite is over the base. Its pullback on each coordinate first applies the inverse bijection to the index and then applies the bijection, recovering that coordinate. The coordinate characterization of maps into affine space gives the identity.
-/
private theorem affineSpace_reindex_comp_reindex_symm {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace.reindex (e : n → m) S ≫ AffineSpace.reindex (e.symm : m → n) S =
      𝟙 (AffineSpace m S) := by
  ext1
  · simp
  · rename_i i
    simp
    show (ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e : n → m) S)))
        ((ConcreteCategory.hom (Scheme.Hom.appTop (AffineSpace.reindex (e.symm : m → n) S)))
          (AffineSpace.coord S i)) = AffineSpace.coord S i
    simp

def affineSpaceIsoOfEquiv {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    AffineSpace n S ≅ AffineSpace m S where
  hom := AffineSpace.reindex (e.symm : m → n) S
  inv := AffineSpace.reindex (e : n → m) S
  hom_inv_id := affineSpace_reindex_symm_comp_reindex e S
  inv_hom_id := affineSpace_reindex_comp_reindex_symm e S

@[simp]
/- English proof (authored)
A reindexing map pulls target coordinates back to the source coordinates. The forward isomorphism therefore uses the inverse bijection to send target indices to source indices, as in its definition.
-/
theorem affineSpaceIsoOfEquiv_hom {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).hom = AffineSpace.reindex (e.symm : m → n) S := rfl

@[simp]
/- English proof (authored)
The inverse isomorphism goes in the opposite direction and is defined by reindexing along the original bijection.
-/
theorem affineSpaceIsoOfEquiv_inv {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).inv = AffineSpace.reindex (e : n → m) S := rfl

/- English proof (authored)
Reindexing changes the coordinate labels and preserves the structure morphism. Composing the forward reindexing with the target projection therefore gives the source projection.
-/
theorem affineSpaceIsoOfEquiv_hom_comp_over {n m : Type u} (e : n ≃ m) (S : Scheme.{u}) :
    (affineSpaceIsoOfEquiv e S).hom ≫ (AffineSpace m S ↘ S) = (AffineSpace n S ↘ S) := by
  simp [affineSpaceIsoOfEquiv, AffineSpace.reindex]

/- English proof (authored)
Apply compatibility of coordinate reindexing with the structural projection when the base is the field spectrum.
-/
theorem affineSpaceIsoOfEquiv_hom_comp_toSpec (k : Type u) [Field k] {n m : Type u} (e : n ≃ m) :
    (affineSpaceIsoOfEquiv e (Spec (CommRingCat.of k))).hom ≫ affineSpaceIndexedByToSpec k m =
      affineSpaceIndexedByToSpec k n := by
  exact affineSpaceIsoOfEquiv_hom_comp_over e (Spec (CommRingCat.of k))

def uliftFinSumOneEquiv (n : ℕ) : ULift.{u, 0} (Fin n ⊕ Fin 1) ≃ ULift.{u, 0} (Fin (n + 1)) :=
  Equiv.ulift.trans (finSumFinEquiv.trans Equiv.ulift.symm)

def toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    G.ambient ⟶ affineSpaceIndexedBy k (ULift.{u, 0} (Fin (n + 1))) :=
  φ.hom ≫ affineSpaceInl k n 1 ≫
    (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom

/- English proof (authored)
The map first identifies the ambient scheme with affine space, then includes it as the zero locus of the extra coordinate, and finally reindexes the coordinates by an isomorphism. The middle map is a closed immersion, and the two isomorphisms preserve this property under composition.
-/
theorem isClosedImmersion_toAffineSpaceOfAmbientIso {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    AlgebraicGeometry.IsClosedImmersion (toAffineSpaceOfAmbientIso G n φ) := by
  have h : AlgebraicGeometry.IsClosedImmersion
      (φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) :=
    inferInstance
  exact h

/- English proof (authored)
The last coordinate reindexing respects the projection to the field, as does the inclusion by a zero coordinate. The composite with the field projection therefore reduces to the structural map on the original affine space composed with the given ambient isomorphism. This is the ambient structural map by hypothesis.
-/
theorem toAffineSpaceOfAmbientIso_comp_toSpec {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    toAffineSpaceOfAmbientIso G n φ ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))) =
      G.ambientStruct := by
  have h : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [h]
  simp only [Category.assoc]
  rw [affineSpaceIsoOfEquiv_hom_comp_toSpec, affineSpaceInl_comp_affineSpaceIndexedByToSpec, hφ]

/- English proof (authored)
The inclusion by one zero coordinate has smooth coordinate codimension one. Transport this codimension through the target reindexing, which is over the field, and through the source isomorphism from the ambient scheme. This gives coordinate codimension one for the composite.
-/
theorem hasSmoothCoordCodim_toAffineSpaceOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u}
    [Field k] [CharZero k] {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)}
    (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n))) :
    HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (toAffineSpaceOfAmbientIso G n φ) 1 := by
  have h1 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n ⊕ Fin 1)))
      (affineSpaceInl k n 1) 1 := hasSmoothCoordCodim_affineSpaceInl hsm k n 1
  have h2 : HasSmoothCoordCodim (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom) 1 :=
    h1.comp_iso_hom (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k)))
      (affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin (n + 1))))
      (affineSpaceIsoOfEquiv_hom_comp_toSpec k (uliftFinSumOneEquiv.{u} n))
  have hdef : toAffineSpaceOfAmbientIso G n φ =
      φ.hom ≫ affineSpaceInl k n 1 ≫
        (affineSpaceIsoOfEquiv (uliftFinSumOneEquiv.{u} n) (Spec (CommRingCat.of k))).hom := rfl
  rw [hdef]
  exact h2.iso_hom_comp φ

def presentationOfAmbientIso (hsm : AffineSpaceIsSmooth.{u}) {k : Type u} [Field k] [CharZero k]
    {Y : Scheme.{u}} {p : Y ⟶ Spec (CommRingCat.of k)} (G : EmbeddingDatum k Y p) (n : ℕ)
    (φ : G.ambient ≅ affineSpaceIndexedBy k (ULift.{u, 0} (Fin n)))
    (hφ : φ.hom ≫ affineSpaceIndexedByToSpec k (ULift.{u, 0} (Fin n)) = G.ambientStruct) :
    ClosedEmbeddingIntoAffineSpace G where
  codimBound := 1
  dim := n + 1
  toAffine := toAffineSpaceOfAmbientIso G n φ
  one_le_codimBound := le_rfl
  one_le_dim := Nat.succ_le_succ (Nat.zero_le n)
  isClosedImmersion_toAffine := isClosedImmersion_toAffineSpaceOfAmbientIso G n φ
  toAffine_comp := toAffineSpaceOfAmbientIso_comp_toSpec G n φ hφ
  locallyConstCodim := hasSmoothCoordCodim_toAffineSpaceOfAmbientIso hsm G n φ

def affineSpaceChartPresentation (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u})
    (k : Type u) [Field k] [CharZero k] (Y : Scheme.{u}) [AlgebraicGeometry.IsAffine Y]
    (pY : Y ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType pY] :
    ClosedEmbeddingIntoAffineSpace (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) :=
  presentationOfAmbientIso hsm (affineSpaceEmbeddingDatum hemb hsnc hsm k Y pY) ((hemb k Y pY).choose)
    (Iso.refl _) (by exact Category.id_comp _)

end FunctorialResolution.EmbeddedResolution

end
