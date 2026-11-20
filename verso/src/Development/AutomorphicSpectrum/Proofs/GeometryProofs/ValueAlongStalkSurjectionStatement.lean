import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ValueAlongStalkSurjection
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FValueAlongStalkSurjection.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.value_along_stalk_surjection : ∀ (X₀ X' : Scheme.{0}) (Ω R : Type) [Field Ω] [CommRing R] [IsLocalRing R] (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀) (z : Spec (CommRingCat.of R) ⟶ X') (a : Ω) (r : R), ξ' ≫ π = ξ → Function.Surjective (π.stalkMap (centre z)).hom → ValAt ξ' z a r → ValAt ξ (z ≫ π) a r := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective | exact GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.ValLift.valAt_of_stalkMap_surjective <;> assumption)
