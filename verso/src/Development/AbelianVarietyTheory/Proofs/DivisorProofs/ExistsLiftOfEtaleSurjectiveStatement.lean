import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedSpaceOfIsConnected
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenConnectedComponentOfNoetherianSpace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_lift_of_etale_surjective` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsLiftOfEtaleSurjective.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.exists_lift_of_etale_surjective' : ∀ (K : Type) [Field K] [IsAlgClosed K] (X Y : Scheme.{0}) (π : Y ⟶ X), Etale π → Surjective π → ∀ x : Sp K ⟶ X, ∃ y : Sp K ⟶ Y, y ≫ π = x := by
  first | exact @GlobalTheory.exists_lift_of_etale_surjective | exact GlobalTheory.exists_lift_of_etale_surjective | (intros; apply GlobalTheory.exists_lift_of_etale_surjective; all_goals assumption)
