import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularAtTranslate
import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.TranslateMemIndOrder
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Models
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.DualOrder
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.BT.QFGroup.regularAt_translate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FGeometryProofs%2FRegularAtTranslate.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.regular_at_translate : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (σ : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ Γ.G) (t : T), toUnit (genPt R) ≫ σ = Γ.pt t → ∀ (f : T → FractionRing R) (g : Γ.G.left), Γ.RegularAt f (((toUnit Γ.G ≫ σ) * 𝟙 Γ.G).left g) → Γ.RegularAt (fun h => f (t * h)) g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.QFGroup.regularAt_translate | exact GlobalTheory.CompanionTheory.Ar.BT.QFGroup.regularAt_translate | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.QFGroup.regularAt_translate <;> assumption)
