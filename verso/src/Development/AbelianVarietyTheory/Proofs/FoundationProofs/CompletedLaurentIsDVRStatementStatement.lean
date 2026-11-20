import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CompletedLaurentIsDVRStatement
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.K5.completed_laurent_isDVR | exact GlobalTheory.K5.completed_laurent_isDVR | (intros; apply GlobalTheory.K5.completed_laurent_isDVR <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.completed_laurent_isDVR_statement : ∀ (p : ℕ) [Fact p.Prime], ∃ _ : IsDomain (O0 p), IsDiscreteValuationRing (O0 p) ∧ Irreducible (p : O0 p) := by
  first | exact @GlobalTheory.K5.completed_laurent_isDVR | exact GlobalTheory.K5.completed_laurent_isDVR | (intros; apply GlobalTheory.K5.completed_laurent_isDVR <;> assumption)
