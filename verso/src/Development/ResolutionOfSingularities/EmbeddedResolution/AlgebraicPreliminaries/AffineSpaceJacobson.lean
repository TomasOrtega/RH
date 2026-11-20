import Mathlib

universe u

open AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
Affine space with finitely many coordinates over k is isomorphic to the spectrum of the polynomial ring in those coordinates. The polynomial ring is a finite-type algebra over a field and therefore is a Jacobson ring. Its spectrum is a Jacobson space, and the homeomorphism induced by the scheme isomorphism transfers this property to affine space.
-/
theorem jacobsonSpace_affineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  JacobsonSpace.of_isClosedEmbedding
    (Scheme.homeoOfIso (AffineSpace.SpecIso n (CommRingCat.of k))).isClosedEmbedding

instance instJacobsonSpaceAffineSpace (k : Type u) [Field k] (n : Type u) [Finite n] :
    JacobsonSpace (AffineSpace n (Spec (CommRingCat.of k))) :=
  jacobsonSpace_affineSpace k n

end FunctorialResolution.EmbeddedResolution
