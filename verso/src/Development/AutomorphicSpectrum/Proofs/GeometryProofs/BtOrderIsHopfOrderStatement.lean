import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderIsHopfOrder
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FBtOrderIsHopfOrder.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.btOrder_isHopfOrder : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub | exact GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.btOrder_isHopfOrder_of_finOpenSub <;> assumption)
