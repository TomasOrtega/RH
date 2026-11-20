import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRootInvolutionParabolic
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ChamberFlip.chain_flip` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsRootInvolutionParabolic.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.exists_root_involution_parabolic : ∀ {k : ℕ} (W : Finset (SV k)), IsPar W → ∃ f : SV k → SV k, ∀ u, u ∉ W → IsPar (insert u W) →
  f u ∉ W ∧ f u ≠ u ∧ IsPar (insert (f u) W) ∧ vec u + vec (f u) ∈ aP W ∧ f (f u) = u := by
  first | exact @GlobalTheory.ChamberFlip.chain_flip | exact GlobalTheory.ChamberFlip.chain_flip | (intros; apply GlobalTheory.ChamberFlip.chain_flip <;> assumption)
