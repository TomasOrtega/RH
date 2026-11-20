import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormMulNormalisedAbsPowHalfEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntIndMemSB

open MeasureTheory Matrix ValuativeRel

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CharNormHalf.norm_mul_apow_eq_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormMulNormalisedAbsPowHalfEqOne.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.norm_mul_normalisedAbsPow_half_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (d : ℕ) (χ : kˣ →* ℂˣ), (∀ u : kˣ, valuation k (u : k) = 1 → ‖(χ u : ℂ)‖ = 1) →
    ∀ ϖ : kˣ, GlobalTheory.SplitFlip.IsUnif ϖ → ‖(χ ϖ : ℂ)‖ ^ 2 * (GlobalTheory.SplitWeil.resCard k : ℝ) ^ d = 1 →
    ∀ x : kˣ, ‖(χ x : ℂ) * GlobalTheory.SplitFlip.apow x (-((d : ℂ) / 2))‖ = 1 := by
  first | exact @GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | exact GlobalTheory.CharNormHalf.norm_mul_apow_eq_one | (intros; apply GlobalTheory.CharNormHalf.norm_mul_apow_eq_one <;> assumption)
