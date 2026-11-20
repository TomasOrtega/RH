import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DefiniteQuotientModelExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TypeAsm.embC | exact GlobalTheory.TypeAsm.embC | (intros; apply GlobalTheory.TypeAsm.embC <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.definite_quotient_model_exists : GlobalTheory.TypeAsm.EmbC := by
  first | exact @GlobalTheory.TypeAsm.embC | exact GlobalTheory.TypeAsm.embC | (intros; apply GlobalTheory.TypeAsm.embC <;> assumption)
