import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtTwoOfDifferentiableOnOpen
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HoloNormed.contDiffAt_two_complex` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FContDiffAtTwoOfDifferentiableOnOpen.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.contDiffAt_two_of_differentiableOn_open : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {W : Set E} {w : E}, IsOpen W → w ∈ W → DifferentiableOn ℂ f W → ContDiffAt ℂ 2 f w := by
  first | exact @GlobalTheory.HoloNormed.contDiffAt_two_complex | exact GlobalTheory.HoloNormed.contDiffAt_two_complex | (intros; apply GlobalTheory.HoloNormed.contDiffAt_two_complex <;> assumption)
