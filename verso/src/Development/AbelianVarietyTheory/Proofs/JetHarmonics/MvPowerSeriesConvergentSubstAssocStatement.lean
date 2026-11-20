import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstAssoc
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
open GlobalTheory.ConvSer
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.ConvSer.csub_assoc` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FJetHarmonics%2FMvPowerSeriesConvergentSubstAssoc.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.mvPowerSeriesConvergentSubst_assoc : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (ρ σ τ : Type) [Fintype ρ] [Fintype σ] (s : ρ → MvPowerSeries σ K) (t : σ → MvPowerSeries τ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → (∀ i, Small (t i)) → Bdd S → (∀ j, Small (csub t (s j))) ∧ csub t (csub s S) = csub (fun j => csub t (s j)) S := by
  first | exact @GlobalTheory.ConvSer.csub_assoc | exact GlobalTheory.ConvSer.csub_assoc | (intros; apply GlobalTheory.ConvSer.csub_assoc <;> assumption)
