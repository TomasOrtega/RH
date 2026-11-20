import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.FourierTransformIdentityHolds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.GenModelXiOf
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.LinearExtensionHolds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.RelIndexLeOfPairing

namespace Formalism.L2.PairingIndexBounds.Mv

/- English proof (translation)
The claim follows from `xi_existence_holds`.
-/
theorem xiExists : XiExists := xi_existence_holds
/- English proof (translation)
The claim follows from `xi_intersection_holds`.
-/
theorem xiInter : XiInter := xi_intersection_holds
/- English proof (translation)
The claim follows from `lattice_moves_hold`.
-/
theorem moves : Moves := lattice_moves_hold
/- English proof (translation)
The claim follows from `index_duality_holds`.
-/
theorem indexDual : IndexDual := index_duality_holds
/- English proof (translation)
The claim follows from `linear_extension_holds`.
-/
theorem extendLin : ExtendLin := linear_extension_holds
/- English proof (translation)
The claim follows from `heisenberg_unitary_holds`.
-/
theorem heisU : HeisU := heisenberg_unitary_holds
/- English proof (translation)
The claim follows from `self_intersection_holds`.
-/
theorem interSelf : InterSelf := self_intersection_holds
/- English proof (translation)
The claim follows from `MovesU_of moves indexDual`.
-/
theorem movesU : MovesU := MovesU_of moves indexDual
/- English proof (translation)
The claim follows from `MovesComposeU_of movesU xiExists xiInter`.
-/
theorem movesComposeU : MovesComposeU := MovesComposeU_of movesU xiExists xiInter
/- English proof (translation)
The claim follows from `GenModelXi_of xiExists movesU extendLin`.
-/
theorem genModelXi : GenModelXi := GenModelXi_of xiExists movesU extendLin

end Formalism.L2.PairingIndexBounds.Mv
