import Formalism.FlagUnipotentLattices.PairingOrthogonalComplement
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.SuperdiagonalAdditionInvariance

namespace Formalism.HermitianLatticeCounting.Final.S4

/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.span_character_ring`.
-/
theorem spanCharRing : Formalism.HermitianLatticeCounting.S4.SpanCharRing := Formalism.HermitianLatticeCounting.P.span_character_ring
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.determinant_annihilates`.
-/
theorem detKills : Formalism.HermitianLatticeCounting.S4.DetKills := Formalism.HermitianLatticeCounting.P.determinant_annihilates
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.unimodular_split`.
-/
theorem unimodSplit : Formalism.HermitianLatticeCounting.S4.UnimodSplit := Formalism.HermitianLatticeCounting.P.unimodular_split
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.local_density_product`.
-/
theorem valuation_product_bound : Formalism.HermitianLatticeCounting.S4.ValuationProductBound := Formalism.HermitianLatticeCounting.P.local_density_product
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.involution_well_defined`.
-/
theorem tauWell : Formalism.HermitianLatticeCounting.S4.TauWell := Formalism.HermitianLatticeCounting.P.involution_well_defined
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.pair_second_constant`.
-/
theorem pairing_orthogonal_complement : Formalism.HermitianLatticeCounting.S4.PairingOrthogonalComplement := Formalism.HermitianLatticeCounting.P.pair_second_constant
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.type_class_count`.
-/
theorem typeBeClass : Formalism.HermitianLatticeCounting.S4.TypeBeClass := Formalism.HermitianLatticeCounting.P.type_class_count
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.module_parts_decomposition`.
-/
theorem thMParts : Formalism.HermitianLatticeCounting.S4.ThMParts := Formalism.HermitianLatticeCounting.P.module_parts_decomposition
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.involution_map_linear`.
-/
theorem tauLin : Formalism.HermitianLatticeCounting.S4.TauLin := Formalism.HermitianLatticeCounting.P.involution_map_linear
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.involution_map_hom`.
-/
theorem tauHom : Formalism.HermitianLatticeCounting.S4.TauHom := Formalism.HermitianLatticeCounting.P.involution_map_hom
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.involution_kernel`.
-/
theorem tauKer : Formalism.HermitianLatticeCounting.S4.TauKer := Formalism.HermitianLatticeCounting.P.involution_kernel
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.tuple_jacobian_alt`.
-/
theorem tupleJac : Formalism.HermitianLatticeCounting.S4.TupleJac := Formalism.HermitianLatticeCounting.P.tuple_jacobian_alt
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.hermitian_jacobian`.
-/
theorem hermJac : Formalism.HermitianLatticeCounting.S4.HermJac := Formalism.HermitianLatticeCounting.P.hermitian_jacobian
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.primitive_density_inert`.
-/
theorem primDensityInert : Formalism.HermitianLatticeCounting.S4.PrimDensityInert := Formalism.HermitianLatticeCounting.P.primitive_density_inert
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.primitive_density_split`.
-/
theorem primDensitySplit : Formalism.HermitianLatticeCounting.S4.PrimDensitySplit := Formalism.HermitianLatticeCounting.P.primitive_density_split
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.hermitian_standard_form`.
-/
theorem hermStdForm : Formalism.HermitianLatticeCounting.S4.HermStdForm := Formalism.HermitianLatticeCounting.P.hermitian_standard_form
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.primitive_density_inert_form`.
-/
theorem primDensityInertForm : Formalism.HermitianLatticeCounting.S4.PrimDensityInertForm := Formalism.HermitianLatticeCounting.P.primitive_density_inert_form
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.primitive_density_split_form`.
-/
theorem primDensitySplitForm : Formalism.HermitianLatticeCounting.S4.PrimDensitySplitForm := Formalism.HermitianLatticeCounting.P.primitive_density_split_form
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.overlattice_count_formula`.
-/
theorem overlatticeCount : Formalism.HermitianLatticeCounting.S4.OverlatticeCount := Formalism.HermitianLatticeCounting.P.overlattice_count_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.shared_constant_formula`.
-/
theorem share_first_constant : Formalism.HermitianLatticeCounting.S4.LocalDensityShareBound := Formalism.HermitianLatticeCounting.P.shared_constant_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.hom_count_symmetric_group`.
-/
theorem homCount : Formalism.HermitianLatticeCounting.S4.HomCount := Formalism.HermitianLatticeCounting.P.hom_count_symmetric_group
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.proper_index_formula`.
-/
theorem properIndex : Formalism.HermitianLatticeCounting.S4.ProperIndex := Formalism.HermitianLatticeCounting.P.proper_index_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.dual_capacity_formula`.
-/
theorem dualCap : Formalism.HermitianLatticeCounting.S4.DualCap := Formalism.HermitianLatticeCounting.P.dual_capacity_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.unimodular_hull`.
-/
theorem unimodHull : Formalism.HermitianLatticeCounting.S4.UnimodHull := Formalism.HermitianLatticeCounting.P.unimodular_hull
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.unimodular_rank`.
-/
theorem unimodRank : Formalism.HermitianLatticeCounting.S4.UnimodRank := Formalism.HermitianLatticeCounting.P.unimodular_rank
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.self_dual_lattice_exists`.
-/
theorem bridgeExists : Formalism.HermitianLatticeCounting.S4.BridgeExists := Formalism.HermitianLatticeCounting.P.self_dual_lattice_exists
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.self_dual_lattice_extension`.
-/
theorem bridgeSelfDual : Formalism.HermitianLatticeCounting.S4.BridgeSelfDual := Formalism.HermitianLatticeCounting.P.self_dual_lattice_extension
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.dual_capacity_variant`.
-/
theorem dualCapV : Formalism.HermitianLatticeCounting.S4.DualCapV := Formalism.HermitianLatticeCounting.P.dual_capacity_variant
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.move_congruence`.
-/
theorem moveCong : Formalism.HermitianLatticeCounting.S4.MoveCong := Formalism.HermitianLatticeCounting.P.move_congruence
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.move_involutive`.
-/
theorem moveInvol : Formalism.HermitianLatticeCounting.S4.MoveInvol := Formalism.HermitianLatticeCounting.P.move_involutive
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.move_perpendicular`.
-/
theorem movePerp : Formalism.HermitianLatticeCounting.S4.MovePerp := Formalism.HermitianLatticeCounting.P.move_perpendicular
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.move_perpendicular_extended`.
-/
theorem movePerpX : Formalism.HermitianLatticeCounting.S4.MovePerpX := Formalism.HermitianLatticeCounting.P.move_perpendicular_extended
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.move_admissible`.
-/
theorem moveAdm : Formalism.HermitianLatticeCounting.S4.MoveAdm := Formalism.HermitianLatticeCounting.P.move_admissible
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.isotropic_complement`.
-/
theorem isoComplement : Formalism.HermitianLatticeCounting.S4.IsoComplement := Formalism.HermitianLatticeCounting.P.isotropic_complement
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.same_trace_count`.
-/
theorem sameTrace : Formalism.HermitianLatticeCounting.S4.SameTrace := Formalism.HermitianLatticeCounting.P.same_trace_count
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.same_trace_hypothesis`.
-/
theorem sameTraceHyp : Formalism.HermitianLatticeCounting.S4.SameTraceHyp := Formalism.HermitianLatticeCounting.P.same_trace_hypothesis
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.superdiagonal_addition_invariance`.
-/
theorem superDiagAdd : Formalism.HermitianLatticeCounting.S4.SuperDiagAdd := Formalism.HermitianLatticeCounting.P.superdiagonal_addition_invariance
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.move_preserves_weight`.
-/
theorem moveWeight : Formalism.HermitianLatticeCounting.S4.MoveWeight := Formalism.HermitianLatticeCounting.P.move_preserves_weight
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.move_second_coordinate`.
-/
theorem moveY : Formalism.HermitianLatticeCounting.S4.MoveY := Formalism.HermitianLatticeCounting.P.move_second_coordinate
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.leakage_algebraic_identity`.
-/
theorem leakAlg : Formalism.HermitianLatticeCounting.S4.LeakAlg := Formalism.HermitianLatticeCounting.P.leakage_algebraic_identity
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.leakage_back_map`.
-/
theorem leakBack : Formalism.HermitianLatticeCounting.S4.LeakBack := Formalism.HermitianLatticeCounting.P.leakage_back_map
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.primitive_cancellation`.
-/
theorem primCancel : Formalism.HermitianLatticeCounting.S4.PrimCancel := Formalism.HermitianLatticeCounting.P.primitive_cancellation
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.hermitian_gauss_sum_ring`.
-/
theorem hermGaussRing : Formalism.HermitianLatticeCounting.S4.HermGaussRing := Formalism.HermitianLatticeCounting.P.hermitian_gauss_sum_ring
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.annihilator_size`.
-/
theorem annihSize : Formalism.HermitianLatticeCounting.S4.AnnihSize := Formalism.HermitianLatticeCounting.P.annihilator_size
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.hermitian_gauss_condition`.
-/
theorem hermGaussCond : Formalism.HermitianLatticeCounting.S4.HermGaussCond := Formalism.HermitianLatticeCounting.P.hermitian_gauss_condition
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.gauss_summand_formula`.
-/
theorem gaussSummand : Formalism.HermitianLatticeCounting.S4.GaussSummand := Formalism.HermitianLatticeCounting.P.gauss_summand_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.conditional_count_formula`.
-/
theorem condCount : Formalism.HermitianLatticeCounting.S4.CondCount := Formalism.HermitianLatticeCounting.P.conditional_count_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.gauss_sum_share`.
-/
theorem gaussShare : Formalism.HermitianLatticeCounting.S4.GaussShare := Formalism.HermitianLatticeCounting.P.gauss_sum_share
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.leakage_probability`.
-/
theorem leakProb : Formalism.HermitianLatticeCounting.S4.LeakProb := Formalism.HermitianLatticeCounting.P.leakage_probability
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.leakage_share_bound_alt`.
-/
theorem leakShare : Formalism.HermitianLatticeCounting.S4.LeakShare := Formalism.HermitianLatticeCounting.P.leakage_share_bound_alt
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.matrix_line_sums`.
-/
theorem rowSums : Formalism.HermitianLatticeCounting.S4.RowSums := Formalism.HermitianLatticeCounting.P.matrix_line_sums
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.unfolding_symmetric`.
-/
theorem unfoldSym : Formalism.HermitianLatticeCounting.S4.UnfoldSym := Formalism.HermitianLatticeCounting.P.unfolding_symmetric
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.kernel_average`.
-/
theorem kernelAvg : Formalism.HermitianLatticeCounting.S4.KernelAvg := Formalism.HermitianLatticeCounting.P.kernel_average
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.kernel_average_sum`.
-/
theorem kernelAvgSum : Formalism.HermitianLatticeCounting.S4.KernelAvgSum := Formalism.HermitianLatticeCounting.P.kernel_average_sum
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.maximal_sum_bound`.
-/
theorem maxSum : Formalism.HermitianLatticeCounting.S4.MaxSum := Formalism.HermitianLatticeCounting.P.maximal_sum_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.type_cauchy_schwarz`.
-/
theorem typeCS : Formalism.HermitianLatticeCounting.S4.TypeCS := Formalism.HermitianLatticeCounting.P.type_cauchy_schwarz
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.hermitian_count_assembly`.
-/
theorem assemblyNG : Formalism.HermitianLatticeCounting.S4.AssemblyNG := Formalism.HermitianLatticeCounting.P.hermitian_count_assembly
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.hermitian_count_assembly_of_type`.
-/
theorem assemblyNG2 : Formalism.HermitianLatticeCounting.S4.AssemblyNG2 := Formalism.HermitianLatticeCounting.P.hermitian_count_assembly_of_type
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.hermitian_count_equality`.
-/
theorem equalityNG : Formalism.HermitianLatticeCounting.S4.EqualityNG := Formalism.HermitianLatticeCounting.P.hermitian_count_equality
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.class_number_squares`.
-/
theorem classSquares : Formalism.HermitianLatticeCounting.S4.ClassSquares := Formalism.HermitianLatticeCounting.P.class_number_squares
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.projection_weight_formula`.
-/
theorem projW : Formalism.HermitianLatticeCounting.S4.ProjW := Formalism.HermitianLatticeCounting.P.projection_weight_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.divisor_count_bound`.
-/
theorem divisorCount : Formalism.HermitianLatticeCounting.S4.DivisorCount := Formalism.HermitianLatticeCounting.P.divisor_count_bound
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.weighted_cauchy_schwarz`.
-/
theorem weightedCS : Formalism.HermitianLatticeCounting.S4.WeightedCS := Formalism.HermitianLatticeCounting.P.weighted_cauchy_schwarz
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.orbit_count_formula`.
-/
theorem omCount : Formalism.HermitianLatticeCounting.S4.OmCount := Formalism.HermitianLatticeCounting.P.orbit_count_formula
/- English proof (translation)
The claim follows from `Formalism.HermitianLatticeCounting.P.fourth_reduction_identity`.
-/
theorem step4 : Formalism.HermitianLatticeCounting.S4.Step4 := Formalism.HermitianLatticeCounting.P.fourth_reduction_identity

end Formalism.HermitianLatticeCounting.Final.S4
