import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingChainMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingRChain
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.RingChain.RingMap.mapSt | exact GlobalTheory.RingChain.RingMap.mapSt | (intros; apply GlobalTheory.RingChain.RingMap.mapSt <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.RingChainMap : GlobalTheory.RingChain.MapSt := by
  first | exact @GlobalTheory.RingChain.RingMap.mapSt | exact GlobalTheory.RingChain.RingMap.mapSt | (intros; apply GlobalTheory.RingChain.RingMap.mapSt <;> assumption)
