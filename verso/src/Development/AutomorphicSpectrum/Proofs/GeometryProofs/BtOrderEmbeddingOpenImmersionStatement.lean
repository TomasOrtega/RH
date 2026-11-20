import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingOpenImmersion
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FBtOrderEmbeddingOpenImmersion.lean&line=106#L106)
-/
theorem _root_.GlobalTheory.T.btOrder_embedding_open_immersion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsOpenImmersion j ∧ Γ.TranslatesCover (Γ.btOrder ⊤) j ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover | exact GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.isOpenImmersion_emb_and_translatesCover <;> assumption)
