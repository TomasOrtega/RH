import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLFamRay
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FExistsLFamRay.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.exists_lFam_normOne_of_mod_four_eq_three : ∀ d M : ℕ, d.Prime → d % 4 = 3 → 100 ≤ d → 3 ≤ M → ∃ 𝓕 : LFam, 𝓕.B = (4 * (d : ℝ) * (M : ℝ) ^ 2) ∧ ∀ p : ℕ, p.Prime → 𝓕.lam 0 p ≠ 0 → GlobalTheory.Mem.An.NormOne d M p := by
  first | exact @GlobalTheory.Hk.exists_lFam_ray | exact GlobalTheory.Hk.exists_lFam_ray | (intros; apply GlobalTheory.Hk.exists_lFam_ray <;> assumption)
