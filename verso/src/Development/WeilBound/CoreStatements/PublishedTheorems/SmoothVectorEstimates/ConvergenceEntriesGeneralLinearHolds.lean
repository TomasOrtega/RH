import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.LieAlgebraAction
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorsIntertwiner
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnitChartOperator
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FourierIntegralBound
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.HaarPairing
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ConjugationOnUnits
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.ExistsLogarithmLinear
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PositiveMatrixBlocks
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CornerBlockIndex
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.LatticeLastEntry
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CornerGLContinuity
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InverseDerivativeContinuity
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AlmostEverywhereSphericalOfG1
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AveragingProjection
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.BoundedInvariantL2
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.HeckeOperatorOfAutomorphic
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerFunctional
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorsRegularRepresentation
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.CharacterNondegenerate
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.UnipotentCharacter
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InfiniteFiniteFactorization
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WeilJacquetShalikaLaw
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.GeneralLinearEntryConvergence
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SmoothVectorOrbit
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.AdelicCharacterCondition
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.InductionG11
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.GoodInverseDenseRange
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirrorMap
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MeetOf
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FinitePartOfMeet
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PSmoNorm
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.FiniteInfinitePlaceProduct
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.SameSatTwist
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.PsiDeterminantFlag

namespace PositivityTheory.jumpWindows

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem compositionalInverseSymm : S1 :=
  lie_algebra_action_exists

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem orthogonalSplitPolarizationVanishes : S2 :=
  smooth_vectors_stable_intertwiner

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem addPreservesExpCongruence : S3 :=
  unit_chart_operator_bound compositionalInverseSymm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem expCongruenceExtendsToSum : S4 :=
  valuation_bound_of_three

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hit_valuation_bound : S5 :=
  haar_measure_pairing

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smooth_vectors_conjugation_holds : S6 :=
  conjugation_units_open orthogonalSplitPolarizationVanishes expCongruenceExtendsToSum

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem exists_logarithm_linear_holds : S8 :=
  exists_logarithm_linear

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem positive_matrix_block_product_holds : MirabolicColumnBlock :=
  positive_matrix_block_product

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem mirabolic_induction_step_holds : S7 :=
  mirabolic_induction_step_exists orthogonalSplitPolarizationVanishes addPreservesExpCongruence hit_valuation_bound smooth_vectors_conjugation_holds exists_logarithm_linear_holds positive_matrix_block_product_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lattice_open_last_entry_holds : S9 :=
  lattice_open_last_entry positive_matrix_block_product_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem automorphic_basic_setup_holds : G0 :=
  standard_stabiliser_bound

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem multiplicity_one_holds : G1 :=
  firstGeometricCondition_of_properties compositionalInverseSymm

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem almost_everywhere_spherical : AlmostEverywhereSpherical :=
  almost_everywhere_spherical_of_G1 multiplicity_one_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem averaging_projection_linear_holds : G2a :=
  averaging_projection_linear

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bounded_invariant_L2_holds : G2b :=
  bounded_invariant_functions_in_L2

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem hecke_operator_automorphic_holds : G2c :=
  hecke_operator_of_automorphic automorphic_basic_setup_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem whittaker_functional_exists_holds : G5 :=
  local_group_averaging_tensor

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smooth_vectors_regular_holds : G5b :=
  smooth_vectors_regular_representation orthogonalSplitPolarizationVanishes automorphic_basic_setup_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem whittaker_nondegenerate_holds : G6 :=
  whittaker_nondegenerate_character mirabolic_induction_step_holds positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem whittaker_expansion_cuspidal_holds : G7 :=
  whittaker_expansion_cuspidal orthogonalSplitPolarizationVanishes lattice_open_last_entry_holds positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds smooth_vectors_regular_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem whittaker_factorization_places_holds : FourierInductionSteps :=
  whittaker_factorization_places whittaker_nondegenerate_holds whittaker_expansion_cuspidal_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem whittaker_uniqueness_local_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : G9 :=
  whittaker_uniqueness_local h7 h12 automorphic_basic_setup_holds whittaker_functional_exists_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem convergence_entries_general_linear_holds : PlacewiseToOutsideS :=
  convergence_entries_general_linear automorphic_basic_setup_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smooth_vector_orbit_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : G8 :=
  smooth_vector_orbit_invariance automorphic_basic_setup_holds whittaker_functional_exists_holds smooth_vectors_regular_holds (whittaker_uniqueness_local_holds h7 h12) convergence_entries_general_linear_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem adelic_character_condition_holds : StandardCharacterExists :=
  adelic_character_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem local_uniqueness_auxiliary_holds : FourierUniquenessMirabolic :=
  induction_g11_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem good_inverse_dense_range_holds : WeakApproximationGL :=
  good_inverse_of_G0 automorphic_basic_setup_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem whittaker_support_theorem_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : WhittakerVanishingImpliesZero :=
  mirror_global_of positive_matrix_block_product_holds automorphic_basic_setup_holds whittaker_functional_exists_holds (whittaker_uniqueness_local_holds h7 h12) convergence_entries_general_linear_holds local_uniqueness_auxiliary_holds good_inverse_dense_range_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_part_meets_conditions (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : Meet :=
  meet_of orthogonalSplitPolarizationVanishes positive_matrix_block_product_holds automorphic_basic_setup_holds multiplicity_one_holds almost_everywhere_spherical averaging_projection_linear_holds bounded_invariant_L2_holds hecke_operator_automorphic_holds whittaker_functional_exists_holds smooth_vectors_regular_holds whittaker_factorization_places_holds (smooth_vector_orbit_holds h7 h12) adelic_character_condition_holds (whittaker_support_theorem_holds h7 h12)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_part_of_meet_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : CuspidalIrreducibleSubrep :=
  finite_part_of_meet (finite_part_meets_conditions h7 h12)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smooth_multiplicity_normalized (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : SmoNorm :=
  smonorm_of (finite_part_meets_conditions h7 h12) (finite_part_of_meet_holds h7 h12)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem finite_infinite_product_one_holds : HeckeCharacterRigidity :=
  finite_infinite_product_eq_one

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem smooth_multiplicity_one_holds (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : Smo :=
  smo_of (smooth_multiplicity_normalized h7 h12) finite_infinite_product_one_holds

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem cuspidal_multiplicity_one (h7 : PositivityTheory.JacquetShalikaLocal.L7) (h12 : PositivityTheory.JacquetShalikaLocal.lift_levelP_alt₂) : GlobalTheory.Published.CuspidalMultiplicityOne :=
  mean_convergence_of (smooth_multiplicity_one_holds h7 h12)

end PositivityTheory.jumpWindows
