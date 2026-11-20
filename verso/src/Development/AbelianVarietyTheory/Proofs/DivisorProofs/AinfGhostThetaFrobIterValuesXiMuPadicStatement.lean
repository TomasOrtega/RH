import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfGhostThetaFrobIterValuesXiMuPadic
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAinfGhostThetaFrobIterValuesXiMuPadic.lean&line=54#L54)
-/
theorem _root_.GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), (∀ a, ghost p O 0 a = WittVector.fontaineTheta O p a) ∧ (∀ n a, ghost p O n (ofPadic p O a) = padicToO p O a) ∧ (∀ n, ghost p O n (Sandwich.mu ε) = 0) ∧ ghost p O 0 (xi ε) = 0 ∧ (∀ n, ghost p O (n + 1) (xi ε) = p) ∧ ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a := by
  first | exact @GlobalTheory.PDivLat.ghost_values | exact GlobalTheory.PDivLat.ghost_values | (intros; apply GlobalTheory.PDivLat.ghost_values <;> assumption)
