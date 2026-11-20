import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsApproxPoincareSeriesAtThetaSetupPoints
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.exists_approxAt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsApproxPoincareSeriesAtThetaSetupPoints.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_approxPoincareSeries_at_thetaSetup_points : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i), IsE8 W → ThetaInt F W i → 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → ∃ d : ℕ, 1 ≤ d ∧ ApproxAt X₁ φ d := by
  first | exact @GlobalTheory.Poinc.exists_approxAt | exact GlobalTheory.Poinc.exists_approxAt | (intros; apply GlobalTheory.Poinc.exists_approxAt <;> assumption)
