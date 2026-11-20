import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FixedFrameSelfNormalFormExistsProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFixedFrameSelfNormalFormExistsProof.lean&line=326#L326)
-/
theorem _root_.GlobalTheory.T.fixedFrameSelfNormalFormExists_proof : GlobalTheory.TypeAsm.IdNFC := by
  first | exact @GlobalTheory.IdNF.idNFC_holds | exact GlobalTheory.IdNF.idNFC_holds | (intros; apply GlobalTheory.IdNF.idNFC_holds <;> assumption)
