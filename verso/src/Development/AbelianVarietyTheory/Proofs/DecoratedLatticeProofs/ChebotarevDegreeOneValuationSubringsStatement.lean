import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChebotarevDegreeOneValuationSubrings
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModChebOm
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.chebOmSt_holds | exact GlobalTheory.chebOmSt_holds | (intros; apply GlobalTheory.chebOmSt_holds <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.chebotarev_degreeOne_valuationSubrings : ReciprocityTheory.ChartRestriction.L1.ChebOmSt := by
  first | exact @GlobalTheory.chebOmSt_holds | exact GlobalTheory.chebOmSt_holds | (intros; apply GlobalTheory.chebOmSt_holds <;> assumption)
