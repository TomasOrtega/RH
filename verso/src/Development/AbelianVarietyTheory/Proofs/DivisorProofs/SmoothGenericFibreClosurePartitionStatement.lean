import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGenericFibreClosurePartition
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothGenericFibreClosurePartition.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.disjoint_closure_and_union_eq_univ_of_genericFibre_partition : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)), Smooth f → ∀ C C' : Set X, C ∪ C' = f ⁻¹' {(⊥ : PrimeSpectrum R)} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  first | exact @GlobalTheory.smooth_genericFibre_closure_partition | exact GlobalTheory.smooth_genericFibre_closure_partition | (intros; apply GlobalTheory.smooth_genericFibre_closure_partition <;> assumption)
