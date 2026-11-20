import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC
namespace GlobalTheory

/- English proof (translation)
Establish `hfp : Algebra.FinitePresentation K L` using `Algebra.FinitePresentation.of_finiteType.mp inferInstance`. Establish `: Algebra.FormallyEtale K L` using `Algebra.FormallyEtale.of_isSeparable K L`. Establish `: Algebra.Etale K L` using `⟨inferInstance, inferInstance⟩`. Establish `hs : Algebra.Smooth K L` using `inferInstance`. Prove the components needed by the constructor for the conclusion.

Rewrite using `[HasRingHomProperty.Spec_iff (P := @Smooth)]`. Rewrite using `[RingHom.Smooth]`. Simplify using `only [CommRingCat.hom_ofHom]`. Conclude with `RingHom.smooth_algebraMap.mpr hs`. Prove the components needed by the constructor for the conclusion.

Introduce `x`. Take `⟨y⟩ : Nonempty (Spec (CommRingCat.of L))` from `inferInstance`. Conclude with `⟨y, Subsingleton.elim _ _⟩`.
-/
theorem spec_map_smooth_surjective_of_isSeparable (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L] : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧ Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  have hfp : Algebra.FinitePresentation K L := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  have : Algebra.FormallyEtale K L := Algebra.FormallyEtale.of_isSeparable K L
  have : Algebra.Etale K L := ⟨inferInstance, inferInstance⟩
  have hs : Algebra.Smooth K L := inferInstance
  constructor
  · rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    rw [RingHom.Smooth]
    simp only [CommRingCat.hom_ofHom]
    exact RingHom.smooth_algebraMap.mpr hs
  · constructor
    intro x
    obtain ⟨y⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
    exact ⟨y, Subsingleton.elim _ _⟩

end GlobalTheory
