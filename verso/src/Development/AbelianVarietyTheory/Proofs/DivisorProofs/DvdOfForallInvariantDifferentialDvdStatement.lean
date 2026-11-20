import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdOfForallInvariantDifferentialDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDvdOfForallInvariantDifferentialDvd.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.dvd_of_forall_invariantDifferential_dvd : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (n : ℕ) (a : O) (b : G.A n), (∀ (w : G.dual.omega) (φ : CartierDual O (G.A n)), dUnit O φ = w.1 n → a ∣ φ b) → (∃ z, b = a • z) ∧ ∀ w : G.dual.omega, ∃ φ : CartierDual O (G.A n), dUnit O φ = w.1 n := by
  first | exact @GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | exact GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd | (intros; apply GlobalTheory.PDivGroup.dvd_of_forall_omega_dvd <;> assumption)
