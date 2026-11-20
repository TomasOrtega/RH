import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerFunctionTendstoConstTermExponential
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
import Development.AbelianVarietyTheory.Definitions.Foundations.SiegelNeZeroIff
open scoped MatrixGroups
open GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FModularTowerFunctionTendstoConstTermExponential.lean&line=63#L63)
-/
theorem _root_.GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (h : X.K) (φ : ℂ → ℂ), ContinuousOn φ Hs → X.an h = (φ : Mero) → (∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n) → ∃ B t : ℝ, ∀ z ∈ Hs, t < z.im → ‖φ z - ε ((X.exp h).coeff 0)‖ ≤ B * Real.exp (-(2 * Real.pi * (z.im - t))) := by
  first | exact @GlobalTheory.KZ.ExpBound.bound_at_infinity | exact GlobalTheory.KZ.ExpBound.bound_at_infinity | (intros; apply GlobalTheory.KZ.ExpBound.bound_at_infinity <;> assumption)
