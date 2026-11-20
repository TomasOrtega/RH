import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSeparatesDualLieGhostComponent
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LieHodgeTate.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeTateSeparatesDualLieGhostComponent.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.hodgeTate_separates_dual_lie_ghostComponent : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → (∀ x : G.dual.Lie, (∀ t, x (hodgeTate G t) = 0) → x = 0) ∧ (∀ x : G.dual.Lie, ∃ y : latt G, ∀ t, WittVector.fontaineTheta O p (y.1 t) = x (hodgeTate G t)) := by
  first | exact @GlobalTheory.LieHodgeTate.main | exact GlobalTheory.LieHodgeTate.main | (intros; apply GlobalTheory.LieHodgeTate.main <;> assumption)
