import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartierDualLiftLinearCoefficientsMod
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvDer
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat GlobalTheory.LawDer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCartierDualLiftLinearCoefficientsMod.lean&line=6#L6)
-/
theorem _root_.GlobalTheory.T.exists_cartierDual_lift_linearCoefficients_mod : ∀ (p : ℕ) (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d) (m : Ideal O), (p : O) ∈ m → ∃ n : ℕ, ∀ u : Fin d → O, ∃ φ : G.dual.A n, ∀ F, φ (c.ev n F) - ∑ i, u i * lin F i ∈ m := by
  first | exact @GlobalTheory.QLog.Chart.exists_dual_lift_lin | exact GlobalTheory.QLog.Chart.exists_dual_lift_lin | (intros; apply GlobalTheory.QLog.Chart.exists_dual_lift_lin <;> assumption)
