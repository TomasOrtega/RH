import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TermSumBoundOfPairsAmplitude
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TermSumBoundOfPairsAmplitude
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude | exact GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude | (intros; apply GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.deg_termSumBoundOfPairsAmplitude : GlobalTheory.Core.Deg.TermSumBoundOfPairsAmplitude := by
  first | exact @GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude | exact GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude | (intros; apply GlobalTheory.Core.Deg.termSumBound_of_pairsAmplitude <;> assumption)
