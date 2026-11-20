import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLiftComparisonRelationsAddSmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSmoothLiftComparisonRelationsAddSmul.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.smoothLift_comparisonRelations_add_smul : ∀ (D : Data) (Λ : Lift D), (∀ a b h h', Λ.Rel1 a h → Λ.Rel1 b h' → Λ.Rel1 (a + b) (h + h')) ∧ (∀ (r : D.R) a h, Λ.Rel1 a h → Λ.Rel1 (r • a) (r • h)) ∧ (∀ a b h h', Λ.Rel2 a h → Λ.Rel2 b h' → Λ.Rel2 (a + b) (h + h')) ∧ ∀ (r : D.R) a h, Λ.Rel2 a h → Λ.Rel2 (r • a) (r • h) := by
  first | exact @GlobalTheory.PDForm.rel_add_smul | exact GlobalTheory.PDForm.rel_add_smul | (intros; apply GlobalTheory.PDForm.rel_add_smul <;> assumption)
