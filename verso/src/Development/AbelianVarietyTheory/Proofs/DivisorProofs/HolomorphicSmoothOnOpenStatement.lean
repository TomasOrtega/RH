import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicSmoothOnOpen
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHolomorphicSmoothOnOpen.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.holomorphic_smooth_on_open : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {s : Set (Pt E g)} {φ : Pt E g → ℂ}, IsOpen s → DifferentiableOn ℂ φ s → ContDiffOn ℝ ∞ φ s := by
  first | exact @GlobalTheory.contDiffOn_real_of_differentiableOn_pt | exact GlobalTheory.contDiffOn_real_of_differentiableOn_pt | (intros; apply GlobalTheory.contDiffOn_real_of_differentiableOn_pt <;> assumption)
