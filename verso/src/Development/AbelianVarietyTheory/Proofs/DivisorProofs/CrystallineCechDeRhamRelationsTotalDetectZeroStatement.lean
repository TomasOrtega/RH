import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamRelationsTotalDetectZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDForm.rel_total_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCrystallineCechDeRhamRelationsTotalDetectZero.lean&line=191#L191)
-/
theorem _root_.GlobalTheory.T.crystallineCechDeRham_relations_total_detect_zero : (∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel1 c h) ∧ (∀ h, ∃ c, Λ.Rel1 c h) ∧ ∀ c h, Λ.Rel1 c h → (c = 0 ↔ h = 0)) ∧ ∀ (D : Data) (Λ : Lift D), (∀ c, ∃ h, Λ.Rel2 c h) ∧ (∀ h, ∃ c, Λ.Rel2 c h) ∧ ∀ c h, Λ.Rel2 c h → (c = 0 ↔ h = 0) := by
  first | exact @GlobalTheory.PDForm.rel_total_zero | exact GlobalTheory.PDForm.rel_total_zero | (intros; apply GlobalTheory.PDForm.rel_total_zero <;> assumption)
