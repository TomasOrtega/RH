import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzSliceSeminormLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTemperateGrowthProdMkConst
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSchwartzSliceSeminormLe.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.schwartz_slice_seminorm_le : ∀ {V V' : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup V'] [NormedSpace ℝ V'] (f : 𝓢(V × V', ℂ)) (x' : V') (j k n : ℕ), ‖x'‖ ^ k * SchwartzMap.seminorm ℂ j n (sliceCLM x' f) ≤ SchwartzMap.seminorm ℂ (j + k) n f := by
  first | exact @GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | exact GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le | (intros; apply GlobalTheory.SchwartzFstOp.norm_pow_mul_seminorm_sliceCLM_le <;> assumption)
