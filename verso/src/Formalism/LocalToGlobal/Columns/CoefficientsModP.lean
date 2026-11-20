import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaRoundFreeHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairBDual
import Formalism.LocalToGlobal.Columns.CoefficientsModP.StdDual
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NabDual

namespace Formalism.L2.DIV

/- English proof (translation)
The claim follows from `fockSymTensor_holds`.
-/
theorem fockSTen : FockSTen := fockSymTensor_holds
/- English proof (translation)
The claim follows from `pairingRational_holds`.
-/
theorem pairRat : PairRat := pairingRational_holds
/- English proof (translation)
The claim follows from `actionRational_holds`.
-/
theorem actRat : ActRat := actionRational_holds
/- English proof (translation)
The claim follows from `pairingNondegenerate_holds`.
-/
theorem pairNondeg : PairNondeg := pairingNondegenerate_holds
/- English proof (translation)
The claim follows from `pairingPositive_holds`.
-/
theorem pairPos : PairPos := pairingPositive_holds
/- English proof (translation)
The claim follows from `latticeBasisExists_holds`.
-/
theorem basisAtEx : BasisAtEx := latticeBasisExists_holds
/- English proof (translation)
The claim follows from `deltaIndependence_holds`.
-/
theorem delIndep : DelIndep := deltaIndependence_holds
/- English proof (translation)
The claim follows from `nablaDeltaFree_holds`.
-/
theorem nabDelFree : NabDelFree := nablaDeltaFree_holds
/- English proof (translation)
The claim follows from `nablaDeltaLocal_holds`.
-/
theorem nabDelLoc : NabDelLoc := nablaDeltaLocal_holds
/- English proof (translation)
The claim follows from `nablaDeltaLattice_holds`.
-/
theorem nabDelLattice : NabDelLattice := nablaDeltaLattice_holds
/- English proof (translation)
The claim follows from `tauLatticeLattice_holds`.
-/
theorem tauLatLattice : TauLatLattice := tauLatticeLattice_holds
/- English proof (translation)
The claim follows from `dualFrameLattice_holds`.
-/
theorem dualFrLattice : DualFrLattice := dualFrameLattice_holds
/- English proof (translation)
The claim follows from `dualFrameHdual_holds`.
-/
theorem dualFrHdual : DualFrHdual := dualFrameHdual_holds
/- English proof (translation)
The claim follows from `tauLatticeDual_holds`.
-/
theorem tauLatDual : TauLatDual := tauLatticeDual_holds
/- English proof (translation)
The claim follows from `roundLattice_holds`.
-/
theorem roundLat : RoundLat := roundLattice_holds
/- English proof (translation)
The claim follows from `weyl_eq_dual_nabla_holds`.
-/
theorem weylEqDualNabla : Formalism.GradedWeylDivisibility.WeylEqDualNabla := weyl_eq_dual_nabla_holds
/- English proof (translation)
The claim follows from `pairBDualStd_of weyl_eq_dual_nabla_holds`.
-/
theorem pairBDualStd : PairBDualStd := pairBDualStd_of weyl_eq_dual_nabla_holds
/- English proof (translation)
The claim follows from `pairBDualK_of pairBDualStd`.
-/
theorem pairBDualK : PairBDualK := pairBDualK_of pairBDualStd
/- English proof (translation)
The claim follows from `pairBDual_of pairBDualStd`.
-/
theorem pairBDual : PairBDual := pairBDual_of pairBDualStd
/- English proof (translation)
The claim follows from `nabDelDual_of nablaDeltaDescent_holds pairBDualK`.
-/
theorem nabDelDual : NabDelDual := nabDelDual_of nablaDeltaDescent_holds pairBDualK

end Formalism.L2.DIV
