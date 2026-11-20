import Mathlib
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SchwartzBruhatIntegralGaussianShapeRootOfUnityPh
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Phase.ph_haar_of_shape` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSiegelThetaTransformation%2FSchwartzBruhatIntegralGaussianShapeRootOfUnityPh.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.schwartzBruhatIntegral_gaussianShape_rootOfUnityPhase : ∀ (κ ι : Type) [Fintype κ] [Fintype ι] [DecidableEq ι], ∀ φ : Matrix κ ι ℚ → ℂ, Shape φ → Ph (haar φ) := by
  first | exact @GlobalTheory.Phase.ph_haar_of_shape | exact GlobalTheory.Phase.ph_haar_of_shape | (intros; apply GlobalTheory.Phase.ph_haar_of_shape <;> assumption)
