import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HenselianQuasiFiniteFinitePart
import Mathlib
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FHenselianQuasiFiniteFinitePart.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.henselian_quasi_finite_finite_part : ∀ (R : Type) [CommRing R] [HenselianLocalRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [LocallyQuasiFinite f] [LocallyOfFiniteType f] [IsSeparated f] [QuasiCompact f], ∃ U : X.Opens, IsFinite (U.ι ≫ f) ∧ ∀ x : X, f x = IsLocalRing.closedPoint R → x ∈ U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian | exact GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.exists_isFinite_open_of_henselian <;> assumption)
