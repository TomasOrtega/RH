import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RayClassLFunctionZeroFreeRegion
import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LamIdealOfNotPrimePow
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Hk.ZeroFree.zero_free_region` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FRayClassLFunctionZeroFreeRegion.lean&line=286#L286)
-/
theorem _root_.GlobalTheory.T.rayClassLFunction_zero_free_region : ∃ c : ℝ, 0 < c ∧ ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) (s : ℂ), 3 / 4 ≤ s.re → 𝓕.F χ s = 0 → (χ * χ ≠ 1 ∨ s.im ≠ 0) → s.re < 1 - c / 𝓕.ell s.im := by
  first | exact @GlobalTheory.Hk.ZeroFree.zero_free_region | exact GlobalTheory.Hk.ZeroFree.zero_free_region | (intros; apply GlobalTheory.Hk.ZeroFree.zero_free_region <;> assumption)
