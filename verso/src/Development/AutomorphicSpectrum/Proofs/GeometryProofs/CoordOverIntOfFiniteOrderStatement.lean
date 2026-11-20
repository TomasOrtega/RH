import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordOverIntOfFiniteOrder
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FCoordOverIntOfFiniteOrder.lean&line=269#L269)
-/
theorem _root_.GlobalTheory.T.coord_over_int_of_finite_order : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type) [CommRing o] [Algebra o Ω] [Module.Finite ℤ o] (κ : Type) [Finite κ] (x : κ → Ω), CoordTie o ξ x → ∃ (N : ℕ) (x' : Fin (N + 1) → Ω), CoordTie ℤ ξ x' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite | exact GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.coordTie_int_of_finite <;> assumption)
