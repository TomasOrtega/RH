import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueMuPInfinityHodgeTateLatticeMap
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsUniqueMuPInfinityHodgeTateLatticeMap.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.existsUnique_muPInfinity_hodgeTate_lattice_map : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ g : latt (PDivGroup.mu p O) →ₗ[Ainf p O] latt (const p O), (∀ m m' : latt (PDivGroup.mu p O), (∀ t, m'.1 t = WittVector.frobenius (m.1 t)) → ∀ t, (g m').1 t = WittVector.frobenius ((g m).1 t)) → ∃! f : const p O ⟶ PDivGroup.mu p O, lattMap f = g := by
  first | exact @GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap | exact GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap | (intros; apply GlobalTheory.PDivLat.ConstMu.existsUnique_lattMap <;> assumption)
