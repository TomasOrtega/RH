import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormFormalGroupHeightOneTorsionTower
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FNormFormalGroupHeightOneTorsionTower.lean&line=118#L118)
-/
theorem _root_.GlobalTheory.T.norm_formalGroup_heightOne_torsion_tower : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [Fact p.Prime] (F : FormalGroup K), Intg F.toPowerSeries → ‖PowerSeries.coeff p (nMul F p)‖ = 1 → (∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) → ∀ t : ℕ → K, (∀ n, ‖t n‖ < 1) → t 0 = 0 → t 1 ≠ 0 → (∀ n, ev1 (nMul F p) (t (n + 1)) = t n) → ‖t 1‖ ^ (p - 1) = ‖(p : K)‖ ∧ ‖(p : K)‖ < 1 ∧ (∀ n j, ¬ p ^ n ∣ j → ‖t 1‖ ≤ ‖ev1 (nMul F j) (t n)‖) ∧ ∀ n, ∏ j ∈ Finset.Ico 1 (p ^ n), ‖ev1 (nMul F j) (t n)‖ = ‖(p : K)‖ ^ n := by
  first | exact @GlobalTheory.ConvSer.TowerNorm.tower_norm | exact GlobalTheory.ConvSer.TowerNorm.tower_norm | (intros; apply GlobalTheory.ConvSer.TowerNorm.tower_norm <;> assumption)
