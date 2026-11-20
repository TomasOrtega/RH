import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RepresentationInputsAllPartsStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.SummandFunctionalBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.DeliveryFourRows

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Fc GlobalTheory.Fc.Ind
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicArithmetic%2FThetaCorrespondence%2FThetaPairLifts%2FThirdPlaceSeries%2FDeliveryFourRows.lean&line=18#L18)
-/
theorem _root_.GlobalTheory.T.fire_realBound_thR_frames_at_all : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → ∀ (𝒜 : FamClass) (σ : RawSel _root_.GlobalTheory.Fc.Ind.PointSummands 𝒜), AtAll _root_.GlobalTheory.Fc.Ind.FiringPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.summandRealBound 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.ThresholdPointSummands 𝒜 σ ∧ AtAll _root_.GlobalTheory.Fc.Ind.FramePointSummands 𝒜 σ := by
  first | exact @_root_.GlobalTheory.Fc.Ind.atAll_fourRows' | exact _root_.GlobalTheory.Fc.Ind.atAll_fourRows' | (intros; apply _root_.GlobalTheory.Fc.Ind.atAll_fourRows' <;> assumption)
end
