import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylLatticeSubstIncreasingMapStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NablaSchur
open GlobalTheory.LeviCut
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem _root_.GlobalTheory.T.dualWeylLattice_subst_increasing_map_stable : GlobalTheory.LeviCut.SubstMem := by
  first | exact @GlobalTheory.LeviCut.substMem | exact GlobalTheory.LeviCut.substMem | (intros; apply GlobalTheory.LeviCut.substMem <;> assumption)
