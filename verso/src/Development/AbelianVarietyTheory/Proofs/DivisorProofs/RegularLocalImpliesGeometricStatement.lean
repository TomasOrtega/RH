import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularLocalImpliesGeometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducesPl
open GlobalTheory.DetHT
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DetHT.geoSt_of_regLocSt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRegularLocalImpliesGeometric.lean&line=214#L214)
-/
theorem _root_.GlobalTheory.T.regular_local_implies_geometric : RegLocSt → GeoSt := by
  first | exact @GlobalTheory.DetHT.geoSt_of_regLocSt | exact GlobalTheory.DetHT.geoSt_of_regLocSt | (intros; apply GlobalTheory.DetHT.geoSt_of_regLocSt <;> assumption)
