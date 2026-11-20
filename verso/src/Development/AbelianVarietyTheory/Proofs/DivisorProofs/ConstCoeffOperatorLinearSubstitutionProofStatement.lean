import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstCoeffOperatorLinearSubstitutionProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FConstCoeffOperatorLinearSubstitutionProof.lean&line=116#L116)
-/
theorem _root_.GlobalTheory.T.constCoeffOperatorLinearSubstitution_proof : LinSt := by
  first | exact @GlobalTheory.IsoTriv.linSt_holds | exact GlobalTheory.IsoTriv.linSt_holds | (intros; apply GlobalTheory.IsoTriv.linSt_holds <;> assumption)
