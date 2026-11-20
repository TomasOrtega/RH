import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqBtOrderTop
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FBtOrderEqBtOrderTop.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.btOrder_eq_btOrder_top : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → Γ.btOrder U = Γ.btOrder ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top | exact GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top | (intros; apply GlobalTheory.CompanionTheory.Relay.btOrder_eq_btOrder_top <;> assumption)
