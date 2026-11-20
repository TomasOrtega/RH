import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AinfHodgeTateLatticeConstQpModZpEquiv
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivLat.latt_const_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FAinfHodgeTateLatticeConstQpModZpEquiv.lean&line=32#L32)
-/
theorem _root_.GlobalTheory.T.ainfHodgeTateLattice_constQpModZp_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (const p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, e y = y.1 (constGen p O) := by
  first | exact @GlobalTheory.PDivLat.latt_const_equiv | exact GlobalTheory.PDivLat.latt_const_equiv | (intros; apply GlobalTheory.PDivLat.latt_const_equiv <;> assumption)
