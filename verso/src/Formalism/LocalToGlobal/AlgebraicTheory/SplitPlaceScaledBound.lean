import Formalism.LocalToGlobal.AlgebraicTheory.ColBoundOfPaths
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.XiConn
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EigenFrameDualOf
import ReciprocityTheory.EigenFrames.EigenPf

namespace Formalism.L2.AlgTh

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem xiConn : XiConn := xiConn_of etLoc scalarConst xiSwap
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem split_place_scaled_bound : SelfDualLatticeThetaPadicIntegrality := split_bound_of_xi_lemmas xiEt xiConn
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem eigenFrameDual : EigenFrameDual := eigenFrameDual_of ReciprocityTheory.EigenFramesTheory.eigenFrameDual
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem kerFrame : KerFrame := kerFrame_of eigenFrameDual

end Formalism.L2.AlgTh
