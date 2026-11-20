import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedIntegersAdicComplete
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.K5.o0_isAdicComplete_span_p | exact GlobalTheory.K5.o0_isAdicComplete_span_p | (intros; apply GlobalTheory.K5.o0_isAdicComplete_span_p <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unramified_integers_adic_complete : ∀ (p : ℕ) [Fact p.Prime], IsAdicComplete (Ideal.span {(p : O0 p)}) (O0 p) := by
  first | exact @GlobalTheory.K5.o0_isAdicComplete_span_p | exact GlobalTheory.K5.o0_isAdicComplete_span_p | (intros; apply GlobalTheory.K5.o0_isAdicComplete_span_p <;> assumption)
