import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingCyclotomicTowerLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsDiscreteValuationRingCyclotomicTowerLevel.lean&line=249#L249)
-/
theorem _root_.GlobalTheory.T.isDiscreteValuationRing_cyclotomicTowerLevel : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ), 1 ≤ n → ∃ _ : IsDomain (On p n), IsDiscreteValuationRing (On p n) ∧ Irreducible (xn p n - 1) := by
  first | exact @GlobalTheory.K5.OnDVR.isDVR_On | exact GlobalTheory.K5.OnDVR.isDVR_On | (intros; apply GlobalTheory.K5.OnDVR.isDVR_On <;> assumption)
