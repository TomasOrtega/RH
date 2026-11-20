import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LogCoordinatesExponentIsCoboundary
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CobExactProof.cobExact` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FLogCoordinatesExponentIsCoboundary.lean&line=19#L19)
-/
theorem _root_.GlobalTheory.T.log_coordinates_exponent_is_coboundary : Formalism.L2.KerInert.BeCob.CobExact := by
  first | exact @GlobalTheory.CobExactProof.cobExact | exact GlobalTheory.CobExactProof.cobExact | (intros; apply GlobalTheory.CobExactProof.cobExact <;> assumption)
