import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BtOrderEmbeddingIsoFinite
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FBtOrderEmbeddingIsoFinite.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.btOrder_embedding_iso_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤))), Γ.IsEmb (Γ.btOrder ⊤) j → IsFinite Γ.G.hom → IsIso j := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite | exact GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.FiniteIso.isIso_of_finite <;> assumption)
