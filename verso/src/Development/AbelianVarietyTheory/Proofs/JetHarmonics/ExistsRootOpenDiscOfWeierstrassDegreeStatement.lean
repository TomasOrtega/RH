import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRootOpenDiscOfWeierstrassDegree
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConvSer.exists_root_of_weierstrassDegree` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FExistsRootOpenDiscOfWeierstrassDegree.lean&line=171#L171)
-/
theorem _root_.GlobalTheory.T.exists_root_openDisc_of_weierstrassDegree : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] [IsAlgClosed K] (h : PowerSeries K) (d : ℕ), 0 < d → Intg h → ‖PowerSeries.coeff d h‖ = 1 → (∀ k < d, ‖PowerSeries.coeff k h‖ < 1) → ∃ x : K, ‖x‖ < 1 ∧ ev1 h x = 0 := by
  first | exact @GlobalTheory.ConvSer.exists_root_of_weierstrassDegree | exact GlobalTheory.ConvSer.exists_root_of_weierstrassDegree | (intros; apply GlobalTheory.ConvSer.exists_root_of_weierstrassDegree <;> assumption)
