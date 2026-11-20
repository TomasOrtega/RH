import Mathlib
import Development.AutomorphicSpectrum.Proofs.TwistedProofs.GeneratingFunctionIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FTwistedProofs%2FGeneratingFunctionIdentity.lean&line=120#L120)
-/
theorem _root_.GlobalTheory.T.generating_function_identity : GenFun := by
  first | exact @GlobalTheory.CompanionTheory.InertGenFun.genFun | exact GlobalTheory.CompanionTheory.InertGenFun.genFun | (intros; apply GlobalTheory.CompanionTheory.InertGenFun.genFun <;> assumption)
