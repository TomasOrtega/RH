import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PhEquivShortWeierstrassModel
import Formalism.LocalToGlobal.InertKernelTheory.DefsBeCob
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FSatakeParameters%2FPhEquivShortWeierstrassModel.lean&line=100#L100)
-/
theorem _root_.GlobalTheory.T.phEquiv_shortWeierstrassModel : Formalism.L2.KerInert.BeCob.PhTie := by
  first | exact @GlobalTheory.ShortModelTie.phTie | exact GlobalTheory.ShortModelTie.phTie | (intros; apply GlobalTheory.ShortModelTie.phTie <;> assumption)
