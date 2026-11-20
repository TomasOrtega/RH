import Formalism.FlagUnipotentLattices.LiftUnitaryFixesBase
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LiftingDecomposition

namespace Formalism.HermitianLatticeCounting.Final.S6

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.lifting_fixes_base_vector`.
-/
theorem lift_fixes_base_vector : Formalism.HermitianLatticeCounting.S6.LiftUnitaryFixesBase := Formalism.HermitianLatticeCounting.P.lifting_fixes_base_vector
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.lifting_unitary`.
-/
theorem liftUnitary : Formalism.HermitianLatticeCounting.S6.LiftUnitary := Formalism.HermitianLatticeCounting.P.lifting_unitary
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.lifting_isometry_weight`.
-/
theorem liftIsoW : Formalism.HermitianLatticeCounting.S6.LiftIsoW := Formalism.HermitianLatticeCounting.P.lifting_isometry_weight
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.relIndex_intersection`.
-/
theorem relIndexInter : Formalism.HermitianLatticeCounting.S6.RelIndexInter := Formalism.HermitianLatticeCounting.P.relIndex_intersection
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.index_chain`.
-/
theorem indexChain : Formalism.HermitianLatticeCounting.S6.IndexChain := Formalism.HermitianLatticeCounting.P.index_chain
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.pairs_loss_bound`.
-/
theorem pairsLoss : Formalism.HermitianLatticeCounting.S6.PairsLoss := Formalism.HermitianLatticeCounting.P.pairs_loss_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.ratio_sum_bound`.
-/
theorem ratioSum : Formalism.HermitianLatticeCounting.S6.RatioSum := Formalism.HermitianLatticeCounting.P.ratio_sum_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.ratio_bound_alt`.
-/
theorem ratioBound : Formalism.HermitianLatticeCounting.S6.RatioBound := Formalism.HermitianLatticeCounting.P.ratio_bound_alt
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.equal_rank_close`.
-/
theorem sEqKClose : Formalism.HermitianLatticeCounting.S6.SEqKClose := Formalism.HermitianLatticeCounting.P.equal_rank_close

end Formalism.HermitianLatticeCounting.Final.S6
