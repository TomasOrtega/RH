import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormalGroupLawLogWithLinearPart
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsFormalGroupLawLogWithLinearPart.lean&line=86#L86)
-/
theorem _root_.GlobalTheory.T.exists_formalGroupLaw_log_with_linearPart : ∀ (p : ℕ) [Fact p.Prime] (O C : Type) [CommRing O] [CommRing C] [Algebra O C], IsFrame p C (RingHom.id O) → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O), IsLaw μ → ∀ w : Fin d → O, ∃ f : MvPowerSeries (Fin d) C, constantCoeff f = 0 ∧ (∀ i, lin f i = algebraMap O C (w i)) ∧ cob1 (up C μ) f = 0 := by
  first | exact @GlobalTheory.QLog.exists_log_of_lin | exact GlobalTheory.QLog.exists_log_of_lin | (intros; apply GlobalTheory.QLog.exists_log_of_lin <;> assumption)
