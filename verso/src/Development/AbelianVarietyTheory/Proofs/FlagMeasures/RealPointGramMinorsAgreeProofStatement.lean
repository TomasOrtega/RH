import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPointGramMinorsAgreeProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.TypeAsm.gramC_holds | exact GlobalTheory.TypeAsm.gramC_holds | (intros; apply GlobalTheory.TypeAsm.gramC_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.realPointGramMinorsAgree_proof : GlobalTheory.TypeAsm.GramC := by
  first | exact @GlobalTheory.TypeAsm.gramC_holds | exact GlobalTheory.TypeAsm.gramC_holds | (intros; apply GlobalTheory.TypeAsm.gramC_holds <;> assumption)
