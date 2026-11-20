import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExportFromReciprocityTheoremsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExportStOfReading

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BigOn.exportSt_of_reading_alt` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FExportStOfReading.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exportSt_of_reciprocity_and_casselman_wallach : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.ExportedStatement := by
  first | exact @_root_.GlobalTheory.BigOn.exportSt_of_reading_alt | exact _root_.GlobalTheory.BigOn.exportSt_of_reading_alt | (intros; apply _root_.GlobalTheory.BigOn.exportSt_of_reading_alt <;> assumption)
end
