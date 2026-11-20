import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointCountOfEigenCovolumeHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FPointCountOfEigenCovolumeHypotheses.lean&line=30#L30)
-/
theorem _root_.GlobalTheory.T.point_count_of_eigen_covolume_hypotheses : BridgeSt → EigSt → CovolSt → PointSt := by
  first | exact @GlobalTheory.DetHT.pointSt_of | exact GlobalTheory.DetHT.pointSt_of | (intros; apply GlobalTheory.DetHT.pointSt_of <;> assumption)
