import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaRecognitionLatticeIsoAndTermsAgree
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FThetaRecognitionLatticeIsoAndTermsAgree.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.thetaRecognition_lattice_iso_and_terms_agree : AllMatch fun μ _ _ => μ.A → ∃ e, μ.B e ∧ μ.Term e := by
  first | exact @GlobalTheory.MatchTerm.main | exact GlobalTheory.MatchTerm.main | (intros; apply GlobalTheory.MatchTerm.main <;> assumption)
