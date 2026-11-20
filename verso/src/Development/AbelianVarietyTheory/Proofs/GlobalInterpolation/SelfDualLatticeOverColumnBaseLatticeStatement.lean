import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticeOverColumnBaseLattice
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.OverObj.selfDualOverBase` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FSelfDualLatticeOverColumnBaseLattice.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.selfDualLattice_over_columnBaseLattice : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase := by
  first | exact @GlobalTheory.OverObj.selfDualOverBase | exact GlobalTheory.OverObj.selfDualOverBase | (intros; apply GlobalTheory.OverObj.selfDualOverBase <;> assumption)
