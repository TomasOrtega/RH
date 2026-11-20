import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsImagQuadOrderPairAndEvenTheta
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MomOne.exists_pair_and_isTh` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FExistsImagQuadOrderPairAndEvenTheta.lean&line=169#L169)
-/
theorem _root_.GlobalTheory.T.exists_imagQuadOrder_pair_and_evenTheta : ∀ d : ℕ, d.Prime → d % 16 = 7 → (∃ L : PeriodPair, IsOK d L ∧ L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = discr d) ∧ ∃ θ : ℂ → ℂ, IsTh d θ := by
  first | exact @GlobalTheory.MomOne.exists_pair_and_isTh | exact GlobalTheory.MomOne.exists_pair_and_isTh | (intros; apply GlobalTheory.MomOne.exists_pair_and_isTh <;> assumption)
