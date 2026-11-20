import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfTeichmullerMinusOneDvdOfGhostComponentsZero
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAinfTeichmullerMinusOneDvdOfGhostComponentsZero.lean&line=60#L60)
-/
theorem _root_.GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, (∀ n, ghost p O n a = 0) → Sandwich.mu ε ∣ a := by
  first | exact @GlobalTheory.GhostKer.mu_dvd_of_ghost | exact GlobalTheory.GhostKer.mu_dvd_of_ghost | (intros; apply GlobalTheory.GhostKer.mu_dvd_of_ghost <;> assumption)
