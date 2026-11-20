import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitalIntegralTensorBoundHypProof
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.TensHS.tensC_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FOrbitalIntegralTensorBoundHypProof.lean&line=45#L45)
-/
theorem _root_.GlobalTheory.T.orbitalIntegralTensorBoundHyp_proof : GlobalTheory.TypeAsm.TensC := by
  first | exact @GlobalTheory.TensHS.tensC_holds | exact GlobalTheory.TensHS.tensC_holds | (intros; apply GlobalTheory.TensHS.tensC_holds <;> assumption)
