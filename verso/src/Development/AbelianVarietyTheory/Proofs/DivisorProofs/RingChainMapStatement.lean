import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingChainMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.RingChainMap : GlobalTheory.RingChain.MapSt := by
  first | exact @GlobalTheory.RingChain.RingMap.mapSt | exact GlobalTheory.RingChain.RingMap.mapSt | (intros; apply GlobalTheory.RingChain.RingMap.mapSt <;> assumption)
