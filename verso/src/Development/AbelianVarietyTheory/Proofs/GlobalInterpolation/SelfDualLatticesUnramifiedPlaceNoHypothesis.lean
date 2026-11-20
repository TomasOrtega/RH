import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SelfDualLatticeActions
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DisjointSpanPerpLat
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsOfFixedInt

namespace GlobalTheory.UnramSelfDualClosed

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem selfDualLatticeLemmas : GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeActions.SelfDualLatticeLemmas :=
  GlobalTheory.SelfDualLatticeCompare.selfDualLattices_iff.1 GlobalTheory.UnramSelfDual.selfDualLattices

end GlobalTheory.UnramSelfDualClosed
