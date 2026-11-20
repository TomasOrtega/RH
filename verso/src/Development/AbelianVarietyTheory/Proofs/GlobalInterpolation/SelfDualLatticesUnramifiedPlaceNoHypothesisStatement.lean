import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SelfDualLatticesUnramifiedPlaceNoHypothesis
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeActions
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FGlobalInterpolation%2FSelfDualLatticesUnramifiedPlaceNoHypothesis.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.selfDual_lattices_unramified_place_no_hypothesis : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas := by
  first | exact @GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas | exact GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas | (intros; apply GlobalTheory.UnramSelfDualClosed.selfDualLatticeLemmas <;> assumption)
