import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LieModel
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LieFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `PositivityTheory.UnitarySelfGeneration.lie_free` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FWeilBound%2FCoreStatements%2FHomogeneousNonvanishing%2FLieFree.lean&line=57#L57)
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.lie_free | exact PositivityTheory.UnitarySelfGeneration.lie_free
