import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubOfFinite
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIsFinOpenSubOfFinite.lean&line=47#L47)
-/
theorem _root_.GlobalTheory.T.isFinOpenSub_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (T : Type) [CommGroup T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), IsFinite (U.ι ≫ Γ.G.hom) → (∀ x : Γ.G.left, Γ.G.hom x = IsLocalRing.closedPoint R → x ∈ U) → Γ.IsFinOpenSub U := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.isFinOpenSub_of_closedFibre <;> assumption)
