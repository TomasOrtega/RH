import Mathlib

open CategoryTheory

namespace FunctorialResolution.EmbeddedResolution

/- English proof (authored)
The stalk at x in the affine open is the localization of its section ring at the prime of x. Localization preserves reducedness, so the reducedness of the section ring gives the result.
-/
private theorem isReduced_stalk_of_isAffineOpen {Z : AlgebraicGeometry.Scheme} {V : Z.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V)
    (hred : _root_.IsReduced ↥(Z.presheaf.obj (Opposite.op V))) (x : V) :
    _root_.IsReduced ↥(Z.presheaf.stalk x.1) := by
  have := hV.isLocalization_stalk x
  exact isReduced_localizationPreserves (hV.primeIdealOf x).asIdeal.primeCompl
    ↥(Z.presheaf.stalk x.1) hred

/- English proof (authored)
On the affine open U the kernel ideal of f is the kernel of pullback on sections. Quotienting by this kernel gives a ring that injects into the section ring on the inverse image in W. That section ring is reduced because W is reduced, and any subring of a reduced ring is reduced. The section ring of the kernel subscheme on its inverse image of U is isomorphic to this quotient.
-/
private theorem isReduced_presheaf_obj_subscheme_ker {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X)
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] (U : X.affineOpens) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.obj
      (Opposite.op ((TopologicalSpace.Opens.map
        (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U.1))) := by
  have hid : (AlgebraicGeometry.Scheme.Hom.ker f).ideal U
      = RingHom.ker (AlgebraicGeometry.Scheme.Hom.app f U.1).hom := by
    simp
  have hq : _root_.IsReduced (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U) := by
    rw [hid]
    exact isReduced_of_injective (RingHom.kerLift (AlgebraicGeometry.Scheme.Hom.app f U.1).hom)
      (RingHom.kerLift_injective _)
  have hq' : _root_.IsReduced ↥(CommRingCat.of (↥(X.presheaf.obj (Opposite.op U.1)) ⧸
      (AlgebraicGeometry.Scheme.Hom.ker f).ideal U)) := hq
  exact isReduced_of_injective
    ((AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).hom.hom)
    (AlgebraicGeometry.Scheme.IdealSheafData.subschemeObjIso
      (AlgebraicGeometry.Scheme.Hom.ker f) U).commRingCatIsoToRingEquiv.injective

/- English proof (authored)
Choose an affine open U around the image of y in X. Its inverse image in the kernel subscheme is affine because the inclusion is a closed immersion. The ring of sections on that inverse image is reduced by the quotient argument. Localize it at the prime of y to obtain the reduced stalk.
-/
private theorem isReduced_stalk_subscheme_ker {W X : AlgebraicGeometry.Scheme} (f : W ⟶ X)
    [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f]
    (y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme) :
    _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) := by
  obtain ⟨U, hU, hyU⟩ : ∃ U : X.Opens, AlgebraicGeometry.IsAffineOpen U ∧
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base y ∈ U :=
    ⟨(X.affineCover.f (X.affineCover.idx _)).opensRange,
      AlgebraicGeometry.isAffineOpen_opensRange _, X.affineCover.covers _⟩
  have hVaff : AlgebraicGeometry.IsAffineOpen ((TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U) :=
    hU.preimage (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι
  have hyV : y ∈ (TopologicalSpace.Opens.map
      (AlgebraicGeometry.Scheme.Hom.ker f).subschemeι.base).obj U := hyU
  have hred := isReduced_presheaf_obj_subscheme_ker f ⟨U, hU⟩
  exact isReduced_stalk_of_isAffineOpen hVaff hred ⟨y, hyV⟩

/- English proof (authored)
Apply the stalk computation at each point of the kernel subscheme. Every stalk is reduced, which is the local criterion for the whole scheme to be reduced.
-/
theorem isReduced_subscheme_ker {W X : AlgebraicGeometry.Scheme}
    (f : W ⟶ X) [AlgebraicGeometry.IsReduced W] [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsReduced (AlgebraicGeometry.Scheme.Hom.ker f).subscheme := by
  have : ∀ y : (AlgebraicGeometry.Scheme.Hom.ker f).subscheme,
      _root_.IsReduced ↥((AlgebraicGeometry.Scheme.Hom.ker f).subscheme.presheaf.stalk y) :=
    fun y => isReduced_stalk_subscheme_ker f y
  exact AlgebraicGeometry.isReduced_of_isReduced_stalk _

end FunctorialResolution.EmbeddedResolution
