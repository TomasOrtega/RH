import Development.EtaleCohomology.EtaleTrace.PNIntegralPf
import Development.EtaleCohomology.EtaleTrace.PNBasicPf
import Development.EtaleCohomology.EtaleTrace.GenAwayEvalPf
import Development.EtaleCohomology.EtaleTrace.GenOfAwayPf
import Development.EtaleCohomology.EtaleTrace.GenInPf
import Development.EtaleCohomology.EtaleTrace.ChartOverKPf
import Development.EtaleCohomology.KummerExtensions.EtaleProjectiveChartGenericValuationIdentity
import Development.EtaleCohomology.EtaleTrace.ChartGenOnPf
import Development.EtaleCohomology.EtaleTrace.GenOutChartPfGen
import Development.EtaleCohomology.EtaleTrace.GenOnAgreePf
import Development.EtaleCohomology.EtaleTrace.GenOutGluePf
import Development.EtaleCohomology.EtaleTrace.GenOutPf
import Development.EtaleCohomology.EtaleTrace.GenUseBackPf
import Development.EtaleCohomology.EtaleTrace.GenUsePf
import Development.EtaleCohomology.EtaleTrace.JetSpanPf
import Development.EtaleCohomology.EtaleTrace.TrdegLePf
import Development.EtaleCohomology.EtaleTrace.HomRelPf
import Development.EtaleCohomology.EtaleTrace.StepPf
import Development.EtaleCohomology.EtaleTrace.ProjectPf
import Development.EtaleCohomology.EtaleTrace.JetIndepPf
import Development.EtaleCohomology.EtaleTrace.JetUnramPf
import Development.EtaleCohomology.EtaleTrace.FieldDimPf
import Development.EtaleCohomology.EtaleTrace.FinSurjPfAll
import Development.EtaleCohomology.EtaleTrace.GenEtaleAtBotPf
import Development.EtaleCohomology.EtaleTrace.GenEtalePfData
import Development.EtaleCohomology.EtaleTrace.RatPtInPf
import Development.EtaleCohomology.EtaleTrace.FibreOfEtalePf
import Development.EtaleCohomology.EtaleTrace.FibrePf
import Development.EtaleCohomology.EtaleTrace.LCoverCut

namespace LateralTheory.Fin.LCover
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem projective_space_over_field_integral : LateralTheory.EtaleTrace.Cov.PNIntegral := by
  apply LateralTheory.EtaleTrace.Cov.PNIntegral_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem projective_space_standard_chart_basic_properties : LateralTheory.EtaleTrace.Cov.PNBasic := by
  apply LateralTheory.EtaleTrace.Cov.PNBasic_of <;> first | exact projective_space_over_field_integral
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem homogeneous_localization_away_generator_evaluation : LateralTheory.EtaleTrace.Cov.GenInPf.GenAwayEval := by
  apply LateralTheory.EtaleTrace.Cov.GenInPf.GenAwayEval_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem homogeneous_localization_away_generated_by_coordinates : LateralTheory.EtaleTrace.Cov.GenInPf.GenOfAway := by
  apply LateralTheory.EtaleTrace.Cov.GenInPf.GenOfAway_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem projective_coordinates_generate_inside_chart : LateralTheory.EtaleTrace.Cov.GenIn := by
  apply LateralTheory.EtaleTrace.Cov.GenIn_of <;> first | exact homogeneous_localization_away_generator_evaluation | exact homogeneous_localization_away_generated_by_coordinates
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem projective_chart_ring_hom_over_field : LateralTheory.EtaleTrace.Cov.ChartOverK := by
  apply LateralTheory.EtaleTrace.Cov.ChartOverK_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem projective_chart_generic_section_values_agree : LateralTheory.EtaleTrace.Cov.ChartGenVal := by
  apply SchemeAppLEComposition.Cb.etale_projective_chart_generic_valuation_identity
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem projective_chart_generic_section_on_open : LateralTheory.EtaleTrace.Cov.ChartGenOn := by
  apply LateralTheory.EtaleTrace.Cov.ChartGenOn_of_val <;> first | exact projective_chart_generic_section_values_agree
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem projective_coordinate_sections_generate_on_chart : LateralTheory.EtaleTrace.Cov.GenOutChart := by
  apply LateralTheory.EtaleTrace.Cov.GenOutChart_of_two <;> first | exact projective_chart_ring_hom_over_field | exact projective_chart_generic_section_on_open
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem projective_coordinate_sections_agree_on_overlap : LateralTheory.EtaleTrace.Cov.GenOnAgree := by
  apply LateralTheory.EtaleTrace.Cov.GenOnAgree_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem projective_coordinate_sections_glue_across_charts : LateralTheory.EtaleTrace.Cov.GenOutGlue := by
  apply LateralTheory.EtaleTrace.Cov.GenOutGlue_of_agree <;> first | exact projective_coordinate_sections_agree_on_overlap
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem projective_coordinate_sections_generate_outside_hyperplane : LateralTheory.EtaleTrace.Cov.GenOut := by
  apply LateralTheory.EtaleTrace.Cov.GenOut_of <;> first | exact projective_coordinate_sections_generate_on_chart | exact projective_coordinate_sections_glue_across_charts
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem function_field_generators_pull_back_to_chart : LateralTheory.EtaleTrace.Cov.GenUseBack := by
  apply LateralTheory.EtaleTrace.Cov.GenUseBack_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem projective_coordinates_generate_function_field : LateralTheory.EtaleTrace.Cov.GenUse := by
  apply LateralTheory.EtaleTrace.Cov.GenUse_of <;> first | exact function_field_generators_pull_back_to_chart
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem coordinate_differentials_span_function_field_kaehler : LateralTheory.EtaleTrace.Cov.JetSpan := by
  apply LateralTheory.EtaleTrace.Cov.JetSpan_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem function_field_transcendence_degree_le_dim : LateralTheory.EtaleTrace.Cov.TrdegLe := by
  apply LateralTheory.EtaleTrace.Cov.TrdegLe_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem homogeneous_relation_coordinate_integral_dependence : LateralTheory.EtaleTrace.Cov.HomRel := by
  apply LateralTheory.EtaleTrace.Cov.HomRel_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem linear_projection_reduce_ambient_dimension : LateralTheory.EtaleTrace.Cov.Step := by
  apply LateralTheory.EtaleTrace.StepPf.Step_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem linear_projection_etale_cover_exists : LateralTheory.EtaleTrace.Cov.Project := by
  apply LateralTheory.EtaleTrace.Cov.Project_of <;> first | exact linear_projection_reduce_ambient_dimension | exact homogeneous_relation_coordinate_integral_dependence
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem generic_linear_forms_independent_differentials : LateralTheory.EtaleTrace.Cov.JetIndep := by
  apply LateralTheory.EtaleTrace.Cov.JetIndep_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem linear_projection_unramified_of_independent_differentials : LateralTheory.EtaleTrace.Cov.JetUnram := by
  apply LateralTheory.EtaleTrace.Cov.JetUnram_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem kaehler_differentials_function_field_rank_eq_dim : LateralTheory.EtaleTrace.Cov.FieldDim := by
  apply LateralTheory.EtaleTrace.Cov.FieldDim_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem linear_projection_finite_surjective_onto_affine_space : LateralTheory.EtaleTrace.Cov.FinSurj := by
  apply LateralTheory.EtaleTrace.Cov.FinSurj_of_full <;> first | exact projective_space_standard_chart_basic_properties
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem finite_cover_etale_at_generic_point : LateralTheory.EtaleTrace.Cov.GenEtaleAtBot := by
  apply LateralTheory.EtaleTrace.Cov.GenEtaleAtBotPf.GenEtaleAtBot_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem finite_surjective_unramified_generically_etale : LateralTheory.EtaleTrace.Cov.GenEtale := by
  apply LateralTheory.EtaleTrace.Cov.GenEtale_of_atBot <;> first | exact finite_cover_etale_at_generic_point
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem rational_point_in_nonempty_open_over_alg_closed : LateralTheory.EtaleTrace.Cov.RatPtIn := by
  apply LateralTheory.EtaleTrace.Cov.RatPtIn_of
/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result.
-/
theorem etale_fibre_over_rational_point_of_etale_restriction : LateralTheory.EtaleTrace.Cov.FibreOfEtale := by
  apply LateralTheory.EtaleTrace.Cov.FibreOfEtale_of
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem finite_cover_etale_fibre_over_rational_point : LateralTheory.EtaleTrace.Cov.Fibre := by
  apply LateralTheory.EtaleTrace.Cov.Fibre_of <;> first | exact finite_surjective_unramified_generically_etale | exact rational_point_in_nonempty_open_over_alg_closed | exact etale_fibre_over_rational_point_of_etale_restriction
/- English proof (translation)
Apply the first step, then apply the next step to every resulting obligation.
-/
theorem etale_finite_cover_of_smooth_variety : LateralTheory.EtaleTrace.LCover := by
  apply LateralTheory.EtaleTrace.Cov.goal_of <;> first | exact projective_space_standard_chart_basic_properties | exact projective_coordinates_generate_inside_chart | exact projective_coordinate_sections_generate_outside_hyperplane | exact projective_coordinates_generate_function_field | exact coordinate_differentials_span_function_field_kaehler | exact function_field_transcendence_degree_le_dim | exact homogeneous_relation_coordinate_integral_dependence | exact linear_projection_reduce_ambient_dimension | exact linear_projection_etale_cover_exists | exact generic_linear_forms_independent_differentials | exact linear_projection_unramified_of_independent_differentials | exact kaehler_differentials_function_field_rank_eq_dim | exact linear_projection_finite_surjective_onto_affine_space | exact finite_cover_etale_fibre_over_rational_point
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem intersectionNumber_baseChange : LateralTheory.EtaleTrace.LCover := etale_finite_cover_of_smooth_variety
end LateralTheory.Fin.LCover
