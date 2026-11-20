import Mathlib

universe u

open AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
The claim follows from `JacobsonSpace.of_isClosedEmbedding (Scheme.homeoOfIso (AffineSpace.SpecIso n (CommRingCat.of k))).isClosedEmbedding`.
-/
theorem jacobsonSpace_affineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  JacobsonSpace.of_isClosedEmbedding
    (Scheme.homeoOfIso (AffineSpace.SpecIso n (CommRingCat.of k))).isClosedEmbedding

instance instJacobsonSpaceAffineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  jacobsonSpace_affineSpace k n

end FunctorialResolution.EmbeddedResolution
