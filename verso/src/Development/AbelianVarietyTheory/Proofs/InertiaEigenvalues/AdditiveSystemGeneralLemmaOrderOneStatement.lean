import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemGeneralLemmaOrderOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PMonE.gl1` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdditiveSystemGeneralLemmaOrderOne.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.additiveSystem_generalLemma_orderOne : GLOnto 1 ∧ GLCount 1 := by
  first | exact @GlobalTheory.PMonE.gl1 | exact GlobalTheory.PMonE.gl1 | (intros; apply GlobalTheory.PMonE.gl1 <;> assumption)
