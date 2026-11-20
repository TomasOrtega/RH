import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StandardPairsExistAtLevelPrime
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TwTransAlt
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.standardPairs_exist_at_levelPrime : GlobalTheory.AdForm.StdEx' := by
  first | exact @GlobalTheory.AdForm.StdExProof.stdEx' | exact GlobalTheory.AdForm.StdExProof.stdEx' | (intros; apply GlobalTheory.AdForm.StdExProof.stdEx' <;> assumption)
