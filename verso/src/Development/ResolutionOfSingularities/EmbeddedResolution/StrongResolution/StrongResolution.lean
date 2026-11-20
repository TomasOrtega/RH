import Mathlib
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

def IsStrongResolution (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
    (s : SequenceOfBlowups X) : Prop :=
  AlgebraicGeometry.Smooth (s.lastStructMap ≫ f) ∧
  AlgebraicGeometry.IsProper s.lastStructMap ∧
  CategoryTheory.IsIso
    (AlgebraicGeometry.morphismRestrict s.lastStructMap f.smoothLocus) ∧
  Dense (s.lastStructMap.base ⁻¹' (f.smoothLocus : Set X)) ∧
  s.CentersLieOver ((smoothLocusComplement f : TopologicalSpace.Closeds X) : Set X) ∧
  IsStrictNormalCrossingsDivisor (reducedInverseImage s.lastStructMap (smoothLocusComplement f))

/- English proof (authored)
A strong resolution rule is defined by requiring its sequence on each quasi-compact reduced input over a characteristic-zero field to satisfy the six strong resolution conditions. Expanding the definition of a strong resolution at that input gives exactly the same conditions in the same order.
-/
theorem isStrongResolutionRule_iff (R : ResolutionRule.{u}) :
    IsStrongResolutionRule R ↔
      ∀ (k : Type u) [Field k] [CharZero k] (X : Scheme.{u})
        (f : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType f]
        [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced X],
        IsStrongResolution k X f (R k X f) :=
  Iff.rfl

end FunctorialResolution.EmbeddedResolution

end
