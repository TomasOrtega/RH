import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StrictFundamentalSetIntegralStabilizerExists
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ConstC
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.strict_fundamentalSet_integralStabilizer_exists : GlobalTheory.TypeAsm.FundC := by
  first | exact @GlobalTheory.TypeAsm.fundC_holds | exact GlobalTheory.TypeAsm.fundC_holds | (intros; apply GlobalTheory.TypeAsm.fundC_holds <;> assumption)
