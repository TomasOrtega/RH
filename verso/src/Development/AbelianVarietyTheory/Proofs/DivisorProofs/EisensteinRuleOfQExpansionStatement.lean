import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinRuleOfQExpansion
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.EisRuleProof.eisRule_of` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FEisensteinRuleOfQExpansion.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.eisenstein_rule_of_q_expansion : GlobalTheory.RealMult.QExpansionOnAll → EisExp → EisMod → EisFourier → TorusForm → EisRule := by
  first | exact @GlobalTheory.EisRuleProof.eisRule_of | exact GlobalTheory.EisRuleProof.eisRule_of | (intros; apply GlobalTheory.EisRuleProof.eisRule_of <;> assumption)
