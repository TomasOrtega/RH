import Formalism.FlagUnipotentLattices.HalfDifferenceL1Bound
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.CoefficientLeOperatorNorm
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExtensionInterSubspace

namespace Formalism.HermitianLatticeCounting.Final.S7

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.threshold_head_region`.
-/
theorem threshHead : Formalism.HermitianLatticeCounting.S7.ThreshHead := Formalism.HermitianLatticeCounting.P.threshold_head_region
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.conjugation_invariant_measure`.
-/
theorem conjInv : Formalism.HermitianLatticeCounting.S7.ConjInv := Formalism.HermitianLatticeCounting.P.conjugation_invariant_measure
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.decay_right_side_bound`.
-/
theorem decay_right_side : Formalism.HermitianLatticeCounting.S7.DecayRightSide := Formalism.HermitianLatticeCounting.P.decay_right_side_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.coefficient_le_operator_norm`.
-/
theorem coeffLeOp : Formalism.HermitianLatticeCounting.S7.CoeffLeOp := Formalism.HermitianLatticeCounting.P.coefficient_le_operator_norm
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.projection_coefficient`.
-/
theorem projCoeff : Formalism.HermitianLatticeCounting.S7.ProjCoeff := Formalism.HermitianLatticeCounting.P.projection_coefficient
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.coefficient_isometry`.
-/
theorem coeffIso : Formalism.HermitianLatticeCounting.S7.CoeffIso := Formalism.HermitianLatticeCounting.P.coefficient_isometry
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.rank_one_case`.
-/
theorem rankOne : Formalism.HermitianLatticeCounting.S7.RankOne := Formalism.HermitianLatticeCounting.P.rank_one_case
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.kernel_bound_bis`.
-/
theorem kernelBound : Formalism.HermitianLatticeCounting.S7.KernelBound := Formalism.HermitianLatticeCounting.P.kernel_bound_bis
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.trace_diagonal_bis`.
-/
theorem traceDiag : Formalism.HermitianLatticeCounting.S7.TraceDiag := Formalism.HermitianLatticeCounting.P.trace_diagonal_bis
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.positive_type_bound`.
-/
theorem posTypeBound : Formalism.HermitianLatticeCounting.S7.PosTypeBound := Formalism.HermitianLatticeCounting.P.positive_type_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.tau_lipschitz_bound`.
-/
theorem tauLip : Formalism.HermitianLatticeCounting.S7.TauLip := Formalism.HermitianLatticeCounting.P.tau_lipschitz_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.delta_small`.
-/
theorem deltaSmall : Formalism.HermitianLatticeCounting.S7.DeltaSmall := Formalism.HermitianLatticeCounting.P.delta_small
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.fibre_count_alt`.
-/
theorem fibreCount : Formalism.HermitianLatticeCounting.S7.FibreCount := Formalism.HermitianLatticeCounting.P.fibre_count_alt
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.dimension_identity`.
-/
theorem dimIdentity : Formalism.HermitianLatticeCounting.S7.DimIdentity := Formalism.HermitianLatticeCounting.P.dimension_identity
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.near_region_product`.
-/
theorem nearProduct : Formalism.HermitianLatticeCounting.S7.NearProduct := Formalism.HermitianLatticeCounting.P.near_region_product
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.log_volume_formula`.
-/
theorem logVolume : Formalism.HermitianLatticeCounting.S7.LogVolume := Formalism.HermitianLatticeCounting.P.log_volume_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.type_count`.
-/
theorem typeCount : Formalism.HermitianLatticeCounting.S7.TypeCount := Formalism.HermitianLatticeCounting.P.type_count
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.far_region_count`.
-/
theorem farCount : Formalism.HermitianLatticeCounting.S7.FarCount := Formalism.HermitianLatticeCounting.P.far_region_count
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.far_region_sum`.
-/
theorem farSum : Formalism.HermitianLatticeCounting.S7.FarSum := Formalism.HermitianLatticeCounting.P.far_region_sum
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.threshold_far_region`.
-/
theorem threshFar : Formalism.HermitianLatticeCounting.S7.ThreshFar := Formalism.HermitianLatticeCounting.P.threshold_far_region
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.far_region_prefactor`.
-/
theorem farPrefactor : Formalism.HermitianLatticeCounting.S7.FarPrefactor := Formalism.HermitianLatticeCounting.P.far_region_prefactor
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.far_region_negligible`.
-/
theorem farNegligible : Formalism.HermitianLatticeCounting.S7.FarNegligible := Formalism.HermitianLatticeCounting.P.far_region_negligible
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.tau_integral_formula`.
-/
theorem tauIntegral : Formalism.HermitianLatticeCounting.S7.TauIntegral := Formalism.HermitianLatticeCounting.P.tau_integral_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.probability_nonzero_index`.
-/
theorem probINonzero : Formalism.HermitianLatticeCounting.S7.ProbINonzero := Formalism.HermitianLatticeCounting.P.probability_nonzero_index
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.gap_pigeonhole`.
-/
theorem gapPigeonhole : Formalism.HermitianLatticeCounting.S7.GapPigeonhole := Formalism.HermitianLatticeCounting.P.gap_pigeonhole
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.covering_radius_bound`.
-/
theorem coverRadius : Formalism.HermitianLatticeCounting.S7.CoverRadius := Formalism.HermitianLatticeCounting.P.covering_radius_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.covering_arithmetic`.
-/
theorem coverArith : Formalism.HermitianLatticeCounting.S7.CoverArith := Formalism.HermitianLatticeCounting.P.covering_arithmetic
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.iterated_supremum_bound`.
-/
theorem iterSup : Formalism.HermitianLatticeCounting.S7.IterSup := Formalism.HermitianLatticeCounting.P.iterated_supremum_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.deep_region_bound`.
-/
theorem deepBound : Formalism.HermitianLatticeCounting.S7.DeepBound := Formalism.HermitianLatticeCounting.P.deep_region_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.deep_region_chain_height`.
-/
theorem deepChainY : Formalism.HermitianLatticeCounting.S7.DeepChainY := Formalism.HermitianLatticeCounting.P.deep_region_chain_height
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.deep_region_bound_height`.
-/
theorem deepBoundY : Formalism.HermitianLatticeCounting.S7.DeepBoundY := Formalism.HermitianLatticeCounting.P.deep_region_bound_height
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.diagonal_splitting`.
-/
theorem diagSplit : Formalism.HermitianLatticeCounting.S7.DiagSplit := Formalism.HermitianLatticeCounting.P.diagonal_splitting
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.final_sum_near_far`.
-/
theorem finalSum : Formalism.HermitianLatticeCounting.S7.FinalSum := Formalism.HermitianLatticeCounting.P.final_sum_near_far

end Formalism.HermitianLatticeCounting.Final.S7
