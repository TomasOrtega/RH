import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingHolomorphicExpLogConvex
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNonvanishingHolomorphicExpLogConvex.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.nonvanishing_holomorphic_exp_log_convex : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] {V : Set F}, IsOpen V → Convex ℝ V → ∀ h : F → ℂ, DifferentiableOn ℂ h V → (∀ x ∈ V, h x ≠ 0) → ∃ a : F → ℂ, DifferentiableOn ℂ a V ∧ ∀ x ∈ V, h x = Complex.exp (a x) := by
  first | exact @GlobalTheory.HoloLog.main | exact GlobalTheory.HoloLog.main | (intros; apply GlobalTheory.HoloLog.main <;> assumption)
