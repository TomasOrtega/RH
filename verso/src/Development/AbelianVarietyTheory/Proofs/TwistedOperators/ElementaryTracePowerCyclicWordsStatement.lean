import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ElementaryTracePowerCyclicWords
import Mathlib
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FElementaryTracePowerCyclicWords.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.elementary_trace_power_cyclic_words : ∀ {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (m : ℕ), Formalism.REAL.etr E (m + 1) = ∑ a : Fin (m + 1) → Fin n, ((GlobalTheory.Dec.cycWord a).map fun p => E p.1 p.2).prod := by
  first | exact @GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord | exact GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord | (intros; apply GlobalTheory.TraceCycWord.etr_succ_eq_sum_cycWord <;> assumption)
