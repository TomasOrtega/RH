import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteAlgebraResiduePointIdempotentsOverOC
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FFiniteAlgebraResiduePointIdempotentsOverOC.lean&line=226#L226)
-/
theorem _root_.GlobalTheory.T.finiteAlgebra_residuePoint_idempotents_over_OC : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] [IsLocalRing O], v.Integers O → ∀ (A : Type) [CommRing A] [Algebra O A] [Module.Finite O A], Finite (A →ₐ[O] IsLocalRing.ResidueField O) ∧ ∃ e : (A →ₐ[O] IsLocalRing.ResidueField O) → A, (∀ c, IsIdempotentElem (e c)) ∧ (∀ c c', c ≠ c' → e c * e c' = 0) ∧ (∑ᶠ c, e c) = 1 ∧ ∀ c c' : A →ₐ[O] IsLocalRing.ResidueField O, c' (e c) = 1 ↔ c = c' := by
  first | exact @GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points | exact GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points | (intros; apply GlobalTheory.FiniteAlgIdem.idempotents_at_residue_points <;> assumption)
