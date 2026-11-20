import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsCptGenResidueFieldGeneric
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIsCptGenResidueFieldGeneric.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.isCptGen_residue_field_generic : ∀ (X : Scheme.{0}), (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ x : X, (∀ y : X, y ⤳ x → y = x) → IsCptGen (Ω := X.residueField x) (X.fromSpecResidueField x) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal | exact GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal | (intros; apply GlobalTheory.CompanionTheory.Ar.isCptGen_of_maximal <;> assumption)
