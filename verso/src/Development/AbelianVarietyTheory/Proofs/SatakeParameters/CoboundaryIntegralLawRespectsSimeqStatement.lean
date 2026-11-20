import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoboundaryIntegralLawRespectsSimeq
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FCoboundaryIntegralLawRespectsSimeq.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.coboundary_integral_law_respects_simeq : Formalism.L2.KerInert.BeCob.CobSimeq := by
  first | exact @GlobalTheory.CobSimeqProof.cobSimeq | exact GlobalTheory.CobSimeqProof.cobSimeq | (intros; apply GlobalTheory.CobSimeqProof.cobSimeq <;> assumption)
