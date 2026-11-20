import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaKeyRuleValuationUnitOfFunctorial
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.KeyCl
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FThetaLawProofs%2FThetaKeyRuleValuationUnitOfFunctorial.lean&line=15#L15)
-/
theorem _root_.GlobalTheory.T.thetaKeyRule_valuationUnit_of_functorial : ∀ κ : Rule, Funct κ → UnitSp κ → ValUnit κ := by
  first | exact @GlobalTheory.KeyValUnit.valUnit | exact GlobalTheory.KeyValUnit.valUnit | (intros; apply GlobalTheory.KeyValUnit.valUnit <;> assumption)
