import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMethodOfEisensteinFacts
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinSimplePoleOfDoublingMethod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FDoublingMethodOfEisensteinFacts.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.doubling_method_of_eisenstein_facts : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.SiegelEisensteinContinuation → GlobalTheory.Published.SiegelEisensteinSimplePole → GlobalTheory.Published.DoublingMethod := by
  first | exact @GlobalTheory.doublingMethod_of_three | exact GlobalTheory.doublingMethod_of_three | (intros; apply GlobalTheory.doublingMethod_of_three <;> assumption)
