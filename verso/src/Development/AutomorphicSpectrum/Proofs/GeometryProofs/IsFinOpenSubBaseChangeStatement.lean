import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFinOpenSubBaseChange
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FIsFinOpenSubBaseChange.lean&line=55#L55)
-/
theorem _root_.GlobalTheory.T.isFinOpenSub_base_change : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ U : Γ.G.left.Opens, Γ.IsFinOpenSub U → Γ'.IsFinOpenSub (F ⁻¹ᵁ U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange | exact GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isFinOpenSub_preimage_baseChange <;> assumption)
