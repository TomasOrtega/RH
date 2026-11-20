import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicLogOnConvex
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConvexHolLog.exists_differentiableOn_log` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHolomorphicLogOnConvex.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.holomorphic_log_on_convex : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] [FiniteDimensional ℂ F] {S : Set F}, Convex ℝ S → IsOpen S → ∀ f : F → ℂ, DifferentiableOn ℂ f S → (∀ x ∈ S, f x ≠ 0) → ∃ L : F → ℂ, DifferentiableOn ℂ L S ∧ ∀ x ∈ S, f x = Complex.exp (L x) := by
  first | exact @GlobalTheory.ConvexHolLog.exists_differentiableOn_log | exact GlobalTheory.ConvexHolLog.exists_differentiableOn_log | (intros; apply GlobalTheory.ConvexHolLog.exists_differentiableOn_log <;> assumption)
