import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AmplitudeBoundAtTermsOfLocalData
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PerRowC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FAmplitudeBoundAtTermsOfLocalData.lean&line=113#L113)
-/
theorem _root_.GlobalTheory.T.amplitudeBound_at_terms_of_localData : GlobalTheory.TypeAsm.LocDatC → GlobalTheory.TypeAsm.TailP → GlobalTheory.TypeAsm.AmpP := by
  first | exact @GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound | exact GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound | (intros; apply GlobalTheory.TypeAsm.AmpTerms.amplitudeBound_of_localData_of_tailBound <;> assumption)
