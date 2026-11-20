import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StabSelfDualLatticeTransitiveOnLength
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.StabilizerLattices
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.StabOrbit.stabTransitive | exact GlobalTheory.StabOrbit.stabTransitive | (intros; apply GlobalTheory.StabOrbit.stabTransitive <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.stabSelfDualLattice_transitive_on_length : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers.StabTransitive := by
  first | exact @GlobalTheory.StabOrbit.stabTransitive | exact GlobalTheory.StabOrbit.stabTransitive | (intros; apply GlobalTheory.StabOrbit.stabTransitive <;> assumption)
