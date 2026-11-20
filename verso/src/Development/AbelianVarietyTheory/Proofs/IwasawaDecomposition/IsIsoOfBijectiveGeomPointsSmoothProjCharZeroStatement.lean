import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfBijectiveGeomPointsSmoothProjCharZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ProjVar

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BijPointsIso.isIso_of_bijective_points` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FIsIsoOfBijectiveGeomPointsSmoothProjCharZero.lean&line=90#L90)
-/
theorem _root_.GlobalTheory.T.isIso_of_bijective_geomPoints_smoothProj_charZero : ∀ (F : Type) [Field F] [CharZero F] (Y₁ Y₂ : Var F) (h : Y₁.X ⟶ Y₂.X), h ≫ Y₂.str = Y₁.str → (∀ (K : Type) [Field K] [IsAlgClosed K], Function.Bijective (fun p : Sp K ⟶ Y₁.X => p ≫ h)) → IsIso h := by
  first | exact @GlobalTheory.BijPointsIso.isIso_of_bijective_points | exact GlobalTheory.BijPointsIso.isIso_of_bijective_points | (intros; apply GlobalTheory.BijPointsIso.isIso_of_bijective_points <;> assumption)
