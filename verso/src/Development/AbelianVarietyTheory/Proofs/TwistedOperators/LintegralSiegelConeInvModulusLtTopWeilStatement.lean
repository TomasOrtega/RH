import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralSiegelConeInvModulusLtTopWeil
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLintegralSiegelConeInvModulusLtTopWeil.lean&line=160#L160)
-/
theorem _root_.GlobalTheory.T.lintegral_siegelCone_inv_modulus_lt_top_weil : ∀ (F : Type) [Field F] [NumberField F] (n r d : ℕ) {c : ℝ}, 0 < c → d < 2 * (n - r) → ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal (∏ i, t i ^ (Module.finrank ℚ F * d)) * ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top | exact GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top | (intros; apply GlobalTheory.SiegelSet.lintegral_cone_modulus_lt_top <;> assumption)
