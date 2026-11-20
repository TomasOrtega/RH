import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSolutionCountOfOrderOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MooreNorm
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FAdditiveSystemIntegralSolutionCountOfOrderOne.lean&line=150#L150)
-/
theorem _root_.GlobalTheory.T.additiveSystemIntegralSolutionCount_of_order_one : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  first | exact @GlobalTheory.PMonE.LinCount.glCount_of_one | exact GlobalTheory.PMonE.LinCount.glCount_of_one | (intros; apply GlobalTheory.PMonE.LinCount.glCount_of_one <;> assumption)
