import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsAffineOfIsAffinePullbackQuotientOfIsNilpotent

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace GlobalTheory.AffineThickening

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Substitute using the available equality. A detailed English derivation is pending.
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
