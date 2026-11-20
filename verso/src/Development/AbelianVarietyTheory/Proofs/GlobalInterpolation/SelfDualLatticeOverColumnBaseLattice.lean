import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SplittingProjection
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OverLatticeIffSelfDualOverBase
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MemLocLatOverLat

namespace GlobalTheory.OverObj

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem selfDualOverBase : GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection.SelfDualOverBase :=
  GlobalTheory.OverCompare.overLattice_iff_selfDualOverBase.mp GlobalTheory.OverLat.overLattice

end GlobalTheory.OverObj
