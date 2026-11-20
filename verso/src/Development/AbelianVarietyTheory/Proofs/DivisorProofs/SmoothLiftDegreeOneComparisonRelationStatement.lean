import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftDegreeOneComparisonRelation
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDForm.CrysCmp.lift_rel1_pull1_cmp1` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothLiftDegreeOneComparisonRelation.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.smoothLift_degreeOne_comparisonRelation : ∀ (D : Data) (Λ : Lift D) (m : IsMor (dp0 D.R) D.s D.κ D.t (RingHom.id D.R) D.i) (c : FirstDeRham D.s), Λ.Rel1 (m.pull1 c) (cmp1 D.s c) := by
  first | exact @GlobalTheory.PDForm.CrysCmp.lift_rel1_pull1_cmp1 | exact GlobalTheory.PDForm.CrysCmp.lift_rel1_pull1_cmp1 | (intros; apply GlobalTheory.PDForm.CrysCmp.lift_rel1_pull1_cmp1 <;> assumption)
