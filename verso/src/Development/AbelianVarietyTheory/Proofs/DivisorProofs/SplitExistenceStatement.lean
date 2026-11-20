import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitExistence
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.split_existence : GlobalTheory.ThK.KP → GlobalTheory.ThK.SplitEx := by
  first | exact @GlobalTheory.ThKSplit.splitEx | exact GlobalTheory.ThKSplit.splitEx | (intros; apply GlobalTheory.ThKSplit.splitEx <;> assumption)
