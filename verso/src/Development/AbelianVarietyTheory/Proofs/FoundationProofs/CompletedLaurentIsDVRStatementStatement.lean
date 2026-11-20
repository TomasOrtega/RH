import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCompletedLaurentIsDVRStatement.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.completed_laurent_isDVR_statement : ∀ (p : ℕ) [Fact p.Prime], ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  first | exact @GlobalTheory.K5.completed_laurent_isDVR | exact GlobalTheory.K5.completed_laurent_isDVR | (intros; apply GlobalTheory.K5.completed_laurent_isDVR <;> assumption)
