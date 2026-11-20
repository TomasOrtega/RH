import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ThetaTransport.thetaTransportLaw` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FHeckeIsogenyThetaGeneratorTransport.lean&line=735#L735)
-/
theorem _root_.GlobalTheory.T.heckeIsogeny_thetaGenerator_transport : GlobalTheory.HeckePointLaw.ThetaTransportLaw := by
  first | exact @GlobalTheory.ThetaTransport.thetaTransportLaw | exact GlobalTheory.ThetaTransport.thetaTransportLaw | (intros; apply GlobalTheory.ThetaTransport.thetaTransportLaw <;> assumption)
