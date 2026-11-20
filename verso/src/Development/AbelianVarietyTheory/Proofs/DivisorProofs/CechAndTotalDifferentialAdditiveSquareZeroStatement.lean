import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechAndTotalDifferentialAdditiveSquareZero
import Development.AbelianVarietyTheory.Definitions.Divisors.IsFlatLift
open GlobalTheory GlobalTheory.DI
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCechAndTotalDifferentialAdditiveSquareZero.lean&line=73#L73)
-/
theorem _root_.GlobalTheory.T.cech_and_total_differential_additive_square_zero : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E), (∀ c c' : Finset ι → E, delta (c + c') = delta c + delta c') ∧ (∀ c c' : Finset ι → E, delta (c - c') = delta c - delta c') ∧ (∀ c c' : Finset ι → E, Dtot d (c + c') = Dtot d c + Dtot d c') ∧ (∀ c c' : Finset ι → E, Dtot d (c - c') = Dtot d c - Dtot d c') ∧ (∀ c : Finset ι → E, delta (delta c) = 0) ∧ ((∀ x, d (d x) = 0) → ∀ c : Finset ι → E, Dtot d (Dtot d c) = 0) := by
  first | exact @GlobalTheory.DI.delta_Dtot_props | exact GlobalTheory.DI.delta_Dtot_props | (intros; apply GlobalTheory.DI.delta_Dtot_props <;> assumption)
