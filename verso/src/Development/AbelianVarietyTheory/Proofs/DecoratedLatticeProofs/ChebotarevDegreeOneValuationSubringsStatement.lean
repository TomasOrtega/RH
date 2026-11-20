import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubrings
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FChebotarevDegreeOneValuationSubrings.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.chebotarev_degreeOne_valuationSubrings : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  first | exact @GlobalTheory.chebOmSt_holds | exact GlobalTheory.chebOmSt_holds | (intros; apply GlobalTheory.chebOmSt_holds <;> assumption)
