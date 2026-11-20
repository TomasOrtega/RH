import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiLogarithmTangentVectorsBasisDualLie
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LieBasisChange.lie_basis` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuasiLogarithmTangentVectorsBasisDualLie.lean&line=103#L103)
-/
theorem _root_.GlobalTheory.T.quasiLogarithm_tangentVectors_basis_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (E : Type) [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (k : ℕ) (e : Fin d ⊕ Fin k → MvPowerSeries (Fin d) E), IsBasis c.μ e → (∀ i, cob1 (up E c.μ) (e (Sum.inl i)) = 0) → ∃ lb : Module.Basis (Fin k) O G.dual.Lie, ∀ j, c.IsLie (e (Sum.inr j)) (lb j) := by
  first | exact @GlobalTheory.LieBasisChange.lie_basis | exact GlobalTheory.LieBasisChange.lie_basis | (intros; apply GlobalTheory.LieBasisChange.lie_basis <;> assumption)
