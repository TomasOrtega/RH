import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeometricallyConnectedSmoothProjModificationOffO
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsoOverOfIsOpenImmersion
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompHS
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGeometricallyConnectedSmoothProjModificationOffO.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.geometricallyConnected_smoothProjModification_offOpen : ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] (sX : X ⟶ Sp F) (n : ℕ) [SmoothOfRelativeDimension n sX] (U : X.Opens) (M : Modif sX U n) [IsIntegral M.X] [GeometricallyConnected sX], (U : Set X).Nonempty → GeometricallyConnected M.str := by
  first | exact @GlobalTheory.ModifGeomConn.geometricallyConnected_modif | exact GlobalTheory.ModifGeomConn.geometricallyConnected_modif | (intros; apply GlobalTheory.ModifGeomConn.geometricallyConnected_modif <;> assumption)
