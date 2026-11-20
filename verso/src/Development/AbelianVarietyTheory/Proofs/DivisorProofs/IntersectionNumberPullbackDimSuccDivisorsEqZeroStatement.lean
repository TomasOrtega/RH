import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackDimSuccDivisorsEqZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntersectionNumberPullbackDimSuccDivisorsEqZero.lean&line=16#L16)
-/
theorem _root_.GlobalTheory.T.intersectionNumber_pullback_dimSuccDivisors_eq_zero : ∀ (F : Type) [Field F] (Y : Var F) (W : Dbl Y), W.Small → ∀ (q : W.Z ⟶ Y.X) [IsDominant q] (y : Fin (Y.dim + 1) → CartierDiv W.Z) (e : Fin (Y.dim + 1) → Y.Dv), (∀ i, IsPull q (y i) (e i)) → W.num y = 0 := by
  first | exact @GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull | exact GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull | (intros; apply GlobalTheory.FlagPush.Dbl.num_eq_zero_of_isPull <;> assumption)
