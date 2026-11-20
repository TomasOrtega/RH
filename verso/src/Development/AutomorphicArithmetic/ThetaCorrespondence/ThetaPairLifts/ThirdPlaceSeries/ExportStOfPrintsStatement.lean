import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportStatementOfDiscreteSeriesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfPrints

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FExportStOfPrints.lean&line=27#L27)
-/
theorem _root_.GlobalTheory.T.exportSt_of_discrete_series_cover : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt | exact _root_.GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt | (intros; apply _root_.GlobalTheory.BigOn.Exp.exportSt_of_hypotheses_alt <;> assumption)
end
