import Formalism.FlagUnipotentLattices.CuspidalityThreshold
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.OperatorHilbertSchmidtNorm

namespace Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.near_region_total_abs`.
-/
theorem nearTotalAbs : Formalism.HermitianLatticeCounting.S7.NearTotalAbs := Formalism.HermitianLatticeCounting.P.near_region_total_abs
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.threshold_cusp_numeric`.
-/
theorem cusp_threshold_bound : Formalism.HermitianLatticeCounting.S7.CuspidalityThreshold := Formalism.HermitianLatticeCounting.P.threshold_cusp_numeric
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.threshold_cusp_operator`.
-/
theorem threshCuspOp : Formalism.HermitianLatticeCounting.S7.ThreshCuspOp := Formalism.HermitianLatticeCounting.P.threshold_cusp_operator
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.probability_zero`.
-/
theorem pZero : Formalism.HermitianLatticeCounting.S7.PZero := Formalism.HermitianLatticeCounting.P.probability_zero
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.cube_multiplication`.
-/
theorem cubeMult : Formalism.HermitianLatticeCounting.S7.CubeMult := Formalism.HermitianLatticeCounting.P.cube_multiplication
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.volume_level`.
-/
theorem volLevel : Formalism.HermitianLatticeCounting.S7.VolLevel := Formalism.HermitianLatticeCounting.P.volume_level
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.deep_region_chain_volume`.
-/
theorem deepChainV : Formalism.HermitianLatticeCounting.S7.DeepChainV := Formalism.HermitianLatticeCounting.P.deep_region_chain_volume

end Formalism.HermitianLatticeCounting.Final.CuspThresholdCounts
