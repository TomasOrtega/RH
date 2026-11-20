import Development.EtaleCohomology.CohomologicalPurity.LeafLocPf
import Development.EtaleCohomology.CohomologicalPurity.LeafShrinkPf
import Development.EtaleCohomology.CohomologicalPurity.LeafRankPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPickPf
import Development.EtaleCohomology.CohomologicalPurity.LeafSpanPf
import Development.EtaleCohomology.CohomologicalPurity.LeafEtPf
import Development.EtaleCohomology.CohomologicalPurity.LeafCoordPf
import Development.EtaleCohomology.CohomologicalPurity.LeafSecPf
import Development.EtaleCohomology.CohomologicalPurity.LeafPolyPf
import Development.EtaleCohomology.CohomologicalPurity.LeafNbhdPf
import Development.EtaleCohomology.CohomologicalPurity.LeafChartCut

namespace LateralTheory.Fin.LeafChart
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.ChartCut.LeafLoc_of` to reduce the goal to its premises.
-/
theorem etale_chart_localization_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafLoc := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafLoc_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.ChartCut.LeafShrink_of` to reduce the goal to its premises.
-/
theorem etale_chart_shrinking_open_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafShrink := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafShrink_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of` to reduce the goal to its premises.
-/
theorem etale_chart_conormal_rank_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafRank := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafRank_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.ChartCut.LeafPick_of` to reduce the goal to its premises.
-/
theorem etale_chart_generator_choice_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPick := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafPick_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafSpanPf.LeafSpan_of` to reduce the goal to its premises.
-/
theorem etale_chart_ideal_span_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSpan := by
  apply LateralTheory.CohomologicalPurity.LeafSpanPf.LeafSpan_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafEtPf.LeafEt_of` to reduce the goal to its premises.
-/
theorem etale_chart_etaleness_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafEt := by
  apply LateralTheory.CohomologicalPurity.LeafEtPf.LeafEt_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.ChartCut.LeafCoord_of <;> first | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds`.
-/
theorem etale_chart_coordinate_functions_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafCoord := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafCoord_of <;> first | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafSecPf.LeafSec_of` to reduce the goal to its premises.
-/
theorem etale_chart_section_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafSec := by
  apply LateralTheory.CohomologicalPurity.LeafSecPf.LeafSec_of
/- English proof (translation)
Apply `LateralTheory.CohomologicalPurity.LeafPolyPf.LeafPoly_of` to reduce the goal to its premises.
-/
theorem etale_chart_polynomial_algebra_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafPoly := by
  apply LateralTheory.CohomologicalPurity.LeafPolyPf.LeafPoly_of
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd_of <;> first | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds`.
-/
theorem etale_chart_neighborhood_property_holds : LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd := by
  apply LateralTheory.CohomologicalPurity.ChartCut.LeafNbhd_of <;> first | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds
/- English proof (translation)
Apply the tactic sequence `apply LateralTheory.CohomologicalPurity.ChartCut.goal_of <;> first | exact etale_chart_localization_property_holds | exact etale_chart_shrinking_open_property_holds | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_ …`.
-/
theorem etale_coordinate_chart_existence : LateralTheory.CohomologicalPurity.LeafChart := by
  apply LateralTheory.CohomologicalPurity.ChartCut.goal_of <;> first | exact etale_chart_localization_property_holds | exact etale_chart_shrinking_open_property_holds | exact etale_chart_conormal_rank_property_holds | exact etale_chart_generator_choice_property_holds | exact etale_chart_ideal_span_property_holds | exact etale_chart_etaleness_property_holds | exact etale_chart_coordinate_functions_property_holds | exact etale_chart_section_property_holds | exact etale_chart_polynomial_algebra_property_holds | exact etale_chart_neighborhood_property_holds
/- English proof (translation)
The claim follows from `etale_coordinate_chart_existence`.
-/
theorem intersectionNumber_baseChange : LateralTheory.CohomologicalPurity.LeafChart := etale_coordinate_chart_existence
end LateralTheory.Fin.LeafChart
