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
A detailed English derivation is pending.
-/
theorem fockSTen : FockSTen := fockSymTensor_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairRat : PairRat := pairingRational_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem actRat : ActRat := actionRational_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairNondeg : PairNondeg := pairingNondegenerate_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairPos : PairPos := pairingPositive_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem basisAtEx : BasisAtEx := latticeBasisExists_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem delIndep : DelIndep := deltaIndependence_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nabDelFree : NabDelFree := nablaDeltaFree_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nabDelLoc : NabDelLoc := nablaDeltaLocal_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nabDelLattice : NabDelLattice := nablaDeltaLattice_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tauLatLattice : TauLatLattice := tauLatticeLattice_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualFrLattice : DualFrLattice := dualFrameLattice_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem dualFrHdual : DualFrHdual := dualFrameHdual_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tauLatDual : TauLatDual := tauLatticeDual_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem roundLat : RoundLat := roundLattice_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem weylEqDualNabla : Formalism.GradedWeylDivisibility.WeylEqDualNabla := weyl_eq_dual_nabla_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairBDualStd : PairBDualStd := pairBDualStd_of weyl_eq_dual_nabla_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairBDualK : PairBDualK := pairBDualK_of pairBDualStd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pairBDual : PairBDual := pairBDual_of pairBDualStd
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem nabDelDual : NabDelDual := nabDelDual_of nablaDeltaDescent_holds pairBDualK

end Formalism.L2.DIV
