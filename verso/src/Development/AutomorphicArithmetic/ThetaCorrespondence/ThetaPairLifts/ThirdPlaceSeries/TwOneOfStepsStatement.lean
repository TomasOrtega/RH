import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTwistOfDiscreteSeriesStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwOneOfSteps

set_option synthInstance.maxHeartbeats 200000

section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FTwOneOfSteps.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.conjTw_of_discrete_series_and_casselman_wallach : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwAdmAlt → _root_.GlobalTheory.BigOn.Exp.TwistCharacter → _root_.GlobalTheory.BigOn.Exp.ConjugateTwist := by
  first | exact @_root_.GlobalTheory.BigOn.Exp.TwConj.conj_tw_of_prints | exact _root_.GlobalTheory.BigOn.Exp.TwConj.conj_tw_of_prints | (intros; apply _root_.GlobalTheory.BigOn.Exp.TwConj.conj_tw_of_prints <;> assumption)
end
