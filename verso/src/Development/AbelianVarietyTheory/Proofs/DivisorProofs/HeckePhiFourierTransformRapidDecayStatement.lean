import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformRapidDecay
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KFacDifferentiable
open NumberField Complex MeasureTheory

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.HeckeTwo.hTrans_rapid_decay` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckePhiFourierTransformRapidDecay.lean&line=292#L292)
-/
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_rapid_decay : ∀ (σ : ℂ), 0 < σ.re → ∀ (y : ℝ), y ≠ 0 → ∀ (N : ℕ), ∃ C : ℝ, ∀ ν : ℝ, ‖GlobalTheory.HeckeTwo.hTrans σ ν y‖ ≤ C * (1 + |ν|) ^ (-(N : ℝ)) := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_rapid_decay | exact GlobalTheory.HeckeTwo.hTrans_rapid_decay | (intros; apply GlobalTheory.HeckeTwo.hTrans_rapid_decay <;> assumption)
