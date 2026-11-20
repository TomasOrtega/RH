import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHomeomorphicActionOfCoverOnP
import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousExptPY
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.PolarU Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PolarU.exists_action_on_p` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FExistsHomeomorphicActionOfCoverOnP.lean&line=80#L80)
-/
theorem _root_.GlobalTheory.T.exists_homeomorphic_action_of_cover_on_p : ∀ (p q : ℕ) (T : GrpData p q) (L : Mat p q → (Fin p → Fin q → ℂ)), ContinuousOn L {g | IsUnit g} → (∀ (k : Mat p q) (B : Fin p → Fin q → ℂ), kᴴ * k = 1 → L (k * NormedSpace.exp (pY B)) = B) → (∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y) → ∀ g : T.G, ∃ ψ : (Fin p → Fin q → ℂ) → (Fin p → Fin q → ℂ), Continuous ψ ∧ Function.Bijective ψ ∧ ∀ B, ∃ κ ∈ T.Kset, T.expt (pY B) * g = κ * T.expt (pY (ψ B)) := by
  first | exact @GlobalTheory.PolarU.exists_action_on_p | exact GlobalTheory.PolarU.exists_action_on_p | (intros; apply GlobalTheory.PolarU.exists_action_on_p <;> assumption)
