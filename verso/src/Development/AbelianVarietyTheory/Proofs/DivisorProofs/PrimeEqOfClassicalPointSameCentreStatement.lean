import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfClassicalPointSameCentre
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPrimeEqOfClassicalPointSameCentre.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.prime_eq_of_classicalPoint_same_centre : ∀ (X : Scheme.{0}) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (y : Sp (OO p) ⟶ X) (y' : Sp (OO q) ⟶ X), y (cPt p) = y' (cPt q) → p = q := by
  first | exact @GlobalTheory.Poinc.eq_of_cPt_eq | exact GlobalTheory.Poinc.eq_of_cPt_eq | (intros; apply GlobalTheory.Poinc.eq_of_cPt_eq <;> assumption)
