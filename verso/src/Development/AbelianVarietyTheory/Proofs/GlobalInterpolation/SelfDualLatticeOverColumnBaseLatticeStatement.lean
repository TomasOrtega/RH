import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.OverObj.selfDualOverBase | exact GlobalTheory.OverObj.selfDualOverBase | (intros; apply GlobalTheory.OverObj.selfDualOverBase <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.selfDualLattice_over_columnBaseLattice : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase := by
  first | exact @GlobalTheory.OverObj.selfDualOverBase | exact GlobalTheory.OverObj.selfDualOverBase | (intros; apply GlobalTheory.OverObj.selfDualOverBase <;> assumption)
