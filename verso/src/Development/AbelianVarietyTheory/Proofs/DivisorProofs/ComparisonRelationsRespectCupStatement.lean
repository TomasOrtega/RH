import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonRelationsRespectCup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDForm.Lift.lift_rel2_cup` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FComparisonRelationsRespectCup.lean&line=187#L187)
-/
theorem _root_.GlobalTheory.T.comparison_relations_respect_cup : ∀ (D : Data) (Λ : Lift D) a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel2 (cup _ a b) (cupHH D.s h h') := by
  first | exact @GlobalTheory.PDForm.Lift.lift_rel2_cup | exact GlobalTheory.PDForm.Lift.lift_rel2_cup | (intros; apply GlobalTheory.PDForm.Lift.lift_rel2_cup <;> assumption)
