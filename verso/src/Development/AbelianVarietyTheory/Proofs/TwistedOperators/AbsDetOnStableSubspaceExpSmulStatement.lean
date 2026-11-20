import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsDetOnStableSubspaceExpSmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.DefClassNum
open Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FAbsDetOnStableSubspaceExpSmul.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.absDetOnStableSubspace_exp_smul : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℂ) (V : Submodule ℂ (Fin n → ℂ)), (∀ y ∈ V, A *ᵥ y ∈ V) → ∃ c : ℝ, ∀ t : ℝ, GlobalTheory.FlagMeas.detOn (NormedSpace.exp (t • A)) V = Real.exp (t * c) := by
  first | exact @GlobalTheory.FlagMeas.detOn_exp_smul | exact GlobalTheory.FlagMeas.detOn_exp_smul | (intros; apply GlobalTheory.FlagMeas.detOn_exp_smul <;> assumption)
