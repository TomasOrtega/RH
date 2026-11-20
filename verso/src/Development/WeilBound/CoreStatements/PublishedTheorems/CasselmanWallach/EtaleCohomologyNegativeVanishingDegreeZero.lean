import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.OrthonormalEigenbasisOfBasic
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.U0Commute
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirPowerCommute
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GelfandCentralHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirRealScalar
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirRealOfCentral
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.NilpotentOfPowerTraces
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.IdentityFiltrationBound
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CommutatorAdjointHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EnvelopingAlgebraGrowthBound
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SymmetricPowerHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ColumnMomentsOfSymmetric
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MatrixActionSingle
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GrowthPolynomialOperator
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.InversePowerBoundHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenbasisOfBasic
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusOfBasic
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenspacesOrthogonalOfCalculus
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisFormSumOfGain
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.WordFiltrationCommute
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.BasisSumOfOrthogonality
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GrowthOfBasic
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.SecondDerivativeHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CompactGroupFacts
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.GroupFactsHolds
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.MaximumPrincipleOfFacts
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenWeightedSumBound
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.KFiniteInclusion
import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.PMaxPr

namespace PositivityTheory.CWB

open PositivityTheory.CW

/- English proof (translation)
The claim follows from `orthonormal_eigenbasis_of_basic`.
-/
theorem word_filtration_basic : A0 := orthonormal_eigenbasis_of_basic

/- English proof (translation)
The claim follows from `word_filtration_of_length`.
-/
theorem aux_statement_7 : A1 := word_filtration_of_length

/- English proof (translation)
The claim follows from `adjoint_stable_filtration`.
-/
theorem filtration_adjoint_stable : FiltrationAdjointStable := adjoint_stable_filtration

/- English proof (translation)
The claim follows from `gelfand_central_holds`.
-/
theorem gelfand_invariants_central : A2 := gelfand_central_holds

/- English proof (translation)
The claim follows from `casimir_eigen_exists`.
-/
theorem casimir_eigenvector_exists : A3 := casimir_eigen_exists

/- English proof (translation)
The claim follows from `casimir_real_of_central gelfand_invariants_central casimir_eigenvector_exists`.
-/
theorem casimir_real_scalar : CasimirIsRealScalar := casimir_real_of_central gelfand_invariants_central casimir_eigenvector_exists

/- English proof (translation)
The claim follows from `nilpotent_of_power_traces`.
-/
theorem power_traces_nilpotent : A4 := nilpotent_of_power_traces

/- English proof (translation)
The claim follows from `commutator_adjoint_holds aux_statement_7`.
-/
theorem commutator_adjoint_lower_order : CommutatorAdjointModLower := commutator_adjoint_holds aux_statement_7

/- English proof (translation)
The claim follows from `normal_nilpotent_of_commutator aux_statement_7 gelfand_invariants_central casimir_eigenvector_exists power_traces_nilpotent commutator_adjoint_lower_order`.
-/
theorem aux_statement_6 : A5 := normal_nilpotent_of_commutator aux_statement_7 gelfand_invariants_central casimir_eigenvector_exists power_traces_nilpotent commutator_adjoint_lower_order

/- English proof (translation)
The claim follows from `SymmetricPowerMatrix word_filtration_basic aux_statement_7 casimir_real_scalar`.
-/
theorem identity_operator_filtration : A6 := SymmetricPowerMatrix word_filtration_basic aux_statement_7 casimir_real_scalar

/- English proof (translation)
The claim follows from `symmetric_power_holds`.
-/
theorem matrix_symmetric_power : A7 := symmetric_power_holds

/- English proof (translation)
The claim follows from `column_moments_of_symmetric matrix_symmetric_power`.
-/
theorem column_moments_bound : ColumnOperatorMoments := column_moments_of_symmetric matrix_symmetric_power

/- English proof (translation)
The claim follows from `second_moment_of_columns word_filtration_basic aux_statement_7 filtration_adjoint_stable casimir_real_scalar aux_statement_6 identity_operator_filtration column_moments_bound`.
-/
theorem second_moment_bound : A8 := second_moment_of_columns word_filtration_basic aux_statement_7 filtration_adjoint_stable casimir_real_scalar aux_statement_6 identity_operator_filtration column_moments_bound

/- English proof (translation)
The claim follows from `a9_of_a0_a1_eigenbasis_a6 word_filtration_basic aux_statement_7 casimir_real_scalar identity_operator_filtration`.
-/
theorem etale_cohomology_vanishing_negative_degree_zero : A9 := a9_of_a0_a1_eigenbasis_a6 word_filtration_basic aux_statement_7 casimir_real_scalar identity_operator_filtration

/- English proof (translation)
The claim follows from `inverse_power_bound_holds`.
-/
theorem inverse_power_square_bound : A10 := inverse_power_bound_holds

/- English proof (translation)
The claim follows from `eigenbasis_of_basic word_filtration_basic`.
-/
theorem orthonormal_eigenbasis_exists : EigenbasisExists := eigenbasis_of_basic word_filtration_basic

/- English proof (translation)
The claim follows from `functional_calculus_of_basic word_filtration_basic`.
-/
theorem functional_calculus : FunctionalCalculusLaws := functional_calculus_of_basic word_filtration_basic

/- English proof (translation)
The claim follows from `eigenspaces_orthogonal_of_calculus word_filtration_basic functional_calculus`.
-/
theorem normal_nilpotent_graded_zero : EigenspacesOrthogonalAlt := eigenspaces_orthogonal_of_calculus word_filtration_basic functional_calculus

/- English proof (translation)
The claim follows from `eigen_gain_of_moments word_filtration_basic second_moment_bound etale_cohomology_vanishing_negative_degree_zero inverse_power_square_bound functional_calculus`.
-/
theorem eigen_gain_high : A12 := eigen_gain_of_moments word_filtration_basic second_moment_bound etale_cohomology_vanishing_negative_degree_zero inverse_power_square_bound functional_calculus

/- English proof (translation)
The claim follows from `basis_sum_of_orthogonality word_filtration_basic functional_calculus normal_nilpotent_graded_zero`.
-/
theorem basis_sum_form_values : BasisSumAsFormValues := basis_sum_of_orthogonality word_filtration_basic functional_calculus normal_nilpotent_graded_zero

/- English proof (translation)
The claim follows from `basis_form_sum_of_gain word_filtration_basic functional_calculus eigen_gain_high basis_sum_form_values`.
-/
theorem eigenspace_form_sum : A13 := basis_form_sum_of_gain word_filtration_basic functional_calculus eigen_gain_high basis_sum_form_values

/- English proof (translation)
The claim follows from `growth_of_basic word_filtration_basic`.
-/
theorem word_length_filtration : B1 := growth_of_basic word_filtration_basic

/- English proof (translation)
The claim follows from `heightFunctionalStatement_of_pairingProperties`.
-/
theorem hilbert_schmidt_growth : B2 := heightFunctionalStatement_of_pairingProperties

/- English proof (translation)
The claim follows from `second_derivative_holds`.
-/
theorem tateTwist_local_to_global_strictlyHenselian : B3 := second_derivative_holds

/- English proof (translation)
The claim follows from `group_facts_holds`.
-/
theorem group_facts : UnitaryGroupFacts := group_facts_holds

/- English proof (translation)
The claim follows from `maximum_principle_of_facts hilbert_schmidt_growth tateTwist_local_to_global_strictlyHenselian group_facts`.
-/
theorem maximum_principle_one_function : MaximumPrincipleVar := maximum_principle_of_facts hilbert_schmidt_growth tateTwist_local_to_global_strictlyHenselian group_facts

/- English proof (translation)
The claim follows from `second_derivatives_of_growth word_length_filtration group_facts`.
-/
theorem second_derivative_sum_squares : SumSquaresSecondDerivative := second_derivatives_of_growth word_length_filtration group_facts

/- English proof (translation)
The claim follows from `eigen_weighted_sum_bound word_filtration_basic functional_calculus`.
-/
theorem lieExponentialMajorant_holds : B5 := eigen_weighted_sum_bound word_filtration_basic functional_calculus

/- English proof (translation)
The claim follows from `maxPr_of casimir_real_scalar orthonormal_eigenbasis_exists eigenspace_form_sum group_facts maximum_principle_one_function second_derivative_sum_squares lieExponentialMajorant_holds`.
-/
theorem maxPr : MaxPr := maxPr_of casimir_real_scalar orthonormal_eigenbasis_exists eigenspace_form_sum group_facts maximum_principle_one_function second_derivative_sum_squares lieExponentialMajorant_holds

end PositivityTheory.CWB
