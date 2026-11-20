import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEqOfHopfEmbedding
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

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FBtOrderEqOfHopfEmbedding.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.btOrder_eq_of_hopf_embedding : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.btOrder_eq_of_open_cover | exact GlobalTheory.CompanionTheory.Ar.BT.btOrder_eq_of_open_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.btOrder_eq_of_open_cover <;> assumption)
