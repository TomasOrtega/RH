import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeRhamClassEqZeroOfPeriodsZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechDeRhamClassEqZeroOfPeriodsZero.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.cechDeRham_class_eq_zero_of_periods_zero : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ x, IsPer u.ex u.Λ x 0 → x = 0 := by
  first | exact @GlobalTheory.CechPer.eq_zero_of_isPer_zero | exact GlobalTheory.CechPer.eq_zero_of_isPer_zero | (intros; apply GlobalTheory.CechPer.eq_zero_of_isPer_zero <;> assumption)
