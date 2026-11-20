import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedNormalFormRelevantTermProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypeAsm.nfExC_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsAdaptedNormalFormRelevantTermProof.lean&line=155#L155)
-/
theorem _root_.GlobalTheory.T.exists_adaptedNormalForm_relevantTerm : GlobalTheory.TypeAsm.NFExC := by
  first | exact @GlobalTheory.TypeAsm.nfExC_holds | exact GlobalTheory.TypeAsm.nfExC_holds | (intros; apply GlobalTheory.TypeAsm.nfExC_holds <;> assumption)
