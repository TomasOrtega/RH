import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalZeroLocalLawOfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocPart
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.ThK.LemF.evZeroLocLaw | exact GlobalTheory.ThK.LemF.evZeroLocLaw | (intros; apply GlobalTheory.ThK.LemF.evZeroLocLaw <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.eval_zero_local_law_of_hypotheses : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.ThK.LemF.EvZeroLocLaw := by
  first | exact @GlobalTheory.ThK.LemF.evZeroLocLaw | exact GlobalTheory.ThK.LemF.evZeroLocLaw | (intros; apply GlobalTheory.ThK.LemF.evZeroLocLaw <;> assumption)
