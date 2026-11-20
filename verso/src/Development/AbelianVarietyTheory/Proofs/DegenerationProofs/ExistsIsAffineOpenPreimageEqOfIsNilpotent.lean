import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.AffineThickening

/- English proof (translation)
Establish `h1` using `IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg`. Establish `: IsClosedImmersion β` using `MorphismProperty.of_isPullback h.flip h1`. Take `⟨O, hO, hO'⟩` from `β.isClosedEmbedding.isInducing.isOpen_iff.mp D'.isOpen`. Establish `e : β ⁻¹ᵁ ⟨O, hO⟩ = D'` using `Opens.ext hO'`. Use `⟨⟨O, hO⟩, ?_, e⟩` and prove the remaining obligations.

Substitute `e` using the available equality. Conclude with `isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hn (CommRingCat.ofHom g) hg rfl ((isPullback_morphismRestrict β ⟨O, hO⟩).paste_vert h) hD'`.
-/
theorem exists_isAffineOpen_preimage_eq_of_isNilpotent (A A' : Type) [CommRing A] [CommRing A']
    (g : A →+* A') (hg : Function.Surjective g) (hn : IsNilpotent (RingHom.ker g))
    (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of A)) (f' : X' ⟶ Spec (CommRingCat.of A'))
    (β : X' ⟶ X) (h : IsPullback β f' f (Spec.map (CommRingCat.ofHom g)))
    (D' : X'.Opens) (hD' : IsAffineOpen D') :
    ∃ D : X.Opens, IsAffineOpen D ∧ β ⁻¹ᵁ D = D' := by
  have h1 := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have : IsClosedImmersion β := MorphismProperty.of_isPullback h.flip h1
  obtain ⟨O, hO, hO'⟩ := β.isClosedEmbedding.isInducing.isOpen_iff.mp D'.isOpen
  have e : β ⁻¹ᵁ ⟨O, hO⟩ = D' := Opens.ext hO'
  refine ⟨⟨O, hO⟩, ?_, e⟩
  subst e
  exact isAffine_of_isPullback_of_isNilpotent (RingHom.ker g) hn (CommRingCat.ofHom g) hg rfl
    ((isPullback_morphismRestrict β ⟨O, hO⟩).paste_vert h) hD'

end GlobalTheory.AffineThickening
