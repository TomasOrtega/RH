import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFanOrderIdealThetaCompactification
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Poinc.idealSt_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFanOrderIdealThetaCompactification.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.exists_fanOrder_ideal_thetaCompactification : IdealSt := by
  first | exact @GlobalTheory.Poinc.idealSt_holds | exact GlobalTheory.Poinc.idealSt_holds | (intros; apply GlobalTheory.Poinc.idealSt_holds <;> assumption)
