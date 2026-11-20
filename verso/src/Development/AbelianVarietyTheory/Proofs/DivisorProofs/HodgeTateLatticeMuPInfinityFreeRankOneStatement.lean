import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeMuPInfinityFreeRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.MuLattice.latt_mu_equiv` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHodgeTateLatticeMuPInfinityFreeRankOne.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.hodgeTateLattice_muPInfinity_free_rank_one : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∃ e : latt (PDivGroup.mu p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, Sandwich.mu ε * e y = y.1 (epsTate hε) := by
  first | exact @GlobalTheory.MuLattice.latt_mu_equiv | exact GlobalTheory.MuLattice.latt_mu_equiv | (intros; apply GlobalTheory.MuLattice.latt_mu_equiv <;> assumption)
