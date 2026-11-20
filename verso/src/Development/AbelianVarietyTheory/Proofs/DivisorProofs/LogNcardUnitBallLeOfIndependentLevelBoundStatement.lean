import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogNcardUnitBallLeOfIndependentLevelBound
import Development.AbelianVarietyTheory.Definitions.Divisors.CharZeroFunctionField
open Filter Topology
open GlobalTheory GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FLogNcardUnitBallLeOfIndependentLevelBound.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.log_ncard_unitBall_le_of_independent_level_bound : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (Λ : AddSubgroup G) (B : ℝ → Set G), IsBallFam Λ B → (B 1).Finite → ∀ (q : ℕ) (T : ℝ), 3 ≤ q → 0 ≤ T → (∀ (r : ℕ) (e : Fin r → G) (n : Fin r → ℕ), LinearIndependent ℤ e → (∀ j, e j ∈ B ((2 / q : ℝ) ^ n j)) → ((∑ j, (n j + 1) : ℕ) : ℝ) ≤ T) → Real.log ((B 1).ncard : ℝ) ≤ Real.log q * T := by
  first | exact @GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound | exact GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound | (intros; apply GlobalTheory.VolBr.log_ncard_unit_ball_le_of_indep_bound <;> assumption)
