import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairsAmplitudeBoundOfTypeBound
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TermSumBoundOfPairsAmplitude
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.pairsAmplitudeBound_of_typeBound : GlobalTheory.Core.Deg.PairsDegOfType := by
  first | exact @GlobalTheory.Core.Deg.pairsDegOfType_holds | exact GlobalTheory.Core.Deg.pairsDegOfType_holds | (intros; apply GlobalTheory.Core.Deg.pairsDegOfType_holds <;> assumption)
