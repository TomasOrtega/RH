import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetBaseChangeOfDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatJet.jetBC_of_grothendieckDeformation_abelianDeRham` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJetBaseChangeOfDeformation.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.jet_base_change_of_deformation : GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → JetBC := by
  first | exact @GlobalTheory.LatJet.jetBC_of_grothendieckDeformation_abelianDeRham | exact GlobalTheory.LatJet.jetBC_of_grothendieckDeformation_abelianDeRham | (intros; apply GlobalTheory.LatJet.jetBC_of_grothendieckDeformation_abelianDeRham <;> assumption)
