import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesCoeffUniformlyContinuousInCoeffsProof
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FSeriesCoeffUniformlyContinuousInCoeffsProof.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.seriesCoeffUniformlyContinuousInCoeffs_proof : ContSt := by
  first | exact @GlobalTheory.IsoTriv.contSt_holds | exact GlobalTheory.IsoTriv.contSt_holds | (intros; apply GlobalTheory.IsoTriv.contSt_holds <;> assumption)
