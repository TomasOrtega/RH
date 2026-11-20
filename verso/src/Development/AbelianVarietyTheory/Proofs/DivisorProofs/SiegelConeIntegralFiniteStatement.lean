import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelConeIntegralFinite
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
open MeasureTheory
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SiegelSet.lintegral_cone_decay_lt_top` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSiegelConeIntegralFinite.lean&line=141#L141)
-/
theorem _root_.GlobalTheory.T.siegel_cone_integral_finite : ∀ (F : Type) [Field F] [NumberField F] (n r : ℕ) {c : ℝ}, 0 < c → ∃ L : ℕ,
    ∫⁻ t in GlobalTheory.SiegelSet.cone r c, ENNReal.ofReal ((1 + ∏ i, t i) ^ L)⁻¹ *
      ENNReal.ofReal ((GlobalTheory.SiegelSet.modulus F n t * ∏ i, t i)⁻¹) < ⊤ := by
  first | exact @GlobalTheory.SiegelSet.lintegral_cone_decay_lt_top | exact GlobalTheory.SiegelSet.lintegral_cone_decay_lt_top | (intros; apply GlobalTheory.SiegelSet.lintegral_cone_decay_lt_top <;> assumption)
