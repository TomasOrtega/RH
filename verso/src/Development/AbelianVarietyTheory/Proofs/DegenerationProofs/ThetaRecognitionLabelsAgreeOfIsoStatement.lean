import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLabelsAgreeOfIso
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FThetaRecognitionLabelsAgreeOfIso.lean&line=338#L338)
-/
theorem _root_.GlobalTheory.T.thetaRecognition_labels_agree_of_iso : AllMatch fun {_} _ {N} {N'} {_} μ _ _ => μ.A → ∀ J : NumD.Iso N N', μ.B J.e → μ.OnG J → (J.lam : _) = μ.c₀ → μ.OnQ J := by
  first | exact @GlobalTheory.LabelsAgree.main | exact GlobalTheory.LabelsAgree.main | (intros; apply GlobalTheory.LabelsAgree.main <;> assumption)
