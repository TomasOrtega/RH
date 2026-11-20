import Mathlib

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

abbrev affineSpaceIndexedBy (k : Type u) [Field k] (n : Type u) : Scheme.{u} :=
  AlgebraicGeometry.AffineSpace n (Spec (CommRingCat.of k))

abbrev affineSpaceIndexedByToSpec (k : Type u) [Field k] (n : Type u) :
    affineSpaceIndexedBy k n ⟶ Spec (CommRingCat.of k) :=
  affineSpaceIndexedBy k n ↘ Spec (CommRingCat.of k)

def pullbackCoord {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) : Γ(Y, ⊤) :=
  f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i)

@[simp]
/- English proof (authored)
The coordinate section associated to f is defined by pulling the indicated affine-space coordinate back to a global section on Y.
-/
theorem pullbackCoord_def {k : Type u} [Field k] {Y : Scheme.{u}} {n : Type u}
    (f : Y ⟶ affineSpaceIndexedBy k n) (i : n) :
    pullbackCoord f i = f.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) i) := rfl

def coordVectorInl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun a => pullbackCoord f (ULift.up a)) (fun _ => 0) i.down

@[simp]
/- English proof (authored)
The first coordinate vector is formed by retaining the pullback coordinates on the first index block and putting zero on the second. A first-block index selects the original pullback section.
-/
theorem coordVectorInl_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (a : Fin n) :
    coordVectorInl n m f (ULift.up (Sum.inl a)) = pullbackCoord f (ULift.up a) := rfl

@[simp]
/- English proof (authored)
At a second-block index, the first coordinate vector takes the prescribed zero value.
-/
theorem coordVectorInl_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin n))) (b : Fin m) :
    coordVectorInl n m f (ULift.up (Sum.inr b)) = 0 := rfl

def coordVectorInr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) :
    ULift.{u} (Fin n ⊕ Fin m) → Γ(Y, ⊤) :=
  fun i => Sum.elim (fun _ => 0) (fun b => pullbackCoord f (ULift.up b)) i.down

@[simp]
/- English proof (authored)
The second coordinate vector has zero in every first-block position, so it is zero at the given index.
-/
theorem coordVectorInr_inl {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (a : Fin n) :
    coordVectorInr n m f (ULift.up (Sum.inl a)) = 0 := rfl

@[simp]
/- English proof (authored)
On the second index block, the second coordinate vector retains the pullback sections. Its value at b is the pullback of the b-th coordinate along f.
-/
theorem coordVectorInr_inr {k : Type u} [Field k] {Y : Scheme.{u}} (n m : ℕ)
    (f : Y ⟶ affineSpaceIndexedBy k (ULift.{u} (Fin m))) (b : Fin m) :
    coordVectorInr n m f (ULift.up (Sum.inr b)) = pullbackCoord f (ULift.up b) := rfl

end FunctorialResolution.EmbeddedResolution
