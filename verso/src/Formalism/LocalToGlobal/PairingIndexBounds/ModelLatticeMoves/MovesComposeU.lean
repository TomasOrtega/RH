import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.FourierTransformIdentityHolds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.GenModelXiOf
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.LinearExtensionHolds
import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.ModelIndexPairings.RelIndexLeOfPairing

namespace Formalism.L2.PairingIndexBounds.Mv

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xiExists : XiExists := xi_existence_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xiInter : XiInter := xi_intersection_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem moves : Moves := lattice_moves_hold
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem indexDual : IndexDual := index_duality_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem extendLin : ExtendLin := linear_extension_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem heisU : HeisU := heisenberg_unitary_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem interSelf : InterSelf := self_intersection_holds
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem movesU : MovesU := MovesU_of moves indexDual
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem movesComposeU : MovesComposeU := MovesComposeU_of movesU xiExists xiInter
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem genModelXi : GenModelXi := GenModelXi_of xiExists movesU extendLin

end Formalism.L2.PairingIndexBounds.Mv
