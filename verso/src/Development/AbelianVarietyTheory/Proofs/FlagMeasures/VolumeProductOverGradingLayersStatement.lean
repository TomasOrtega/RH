import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VolumeProductOverGradingLayers
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IpLEqZeroOfMemSpan
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FVolumeProductOverGradingLayers.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.volume_product_over_grading_layers : ∀ (ι : Type) [Fintype ι] (d m : ℕ) (deg : Fin d → ℕ) (D : ∀ c : ℕ, Set (ι → {i : Fin d // deg i = c} → ℝ)), (ι → ∀ i, deg i < m) → (∀ c, MeasurableSet (D c)) → volume {x : ι → Fin d → ℝ | ∀ c < m, (fun v (i : {i : Fin d // deg i = c}) => x v i.1) ∈ D c} = ∏ c ∈ Finset.range m, volume (D c) := by
  first | exact @GlobalTheory.LayerBox.volume_layer_box | exact GlobalTheory.LayerBox.volume_layer_box | (intros; apply GlobalTheory.LayerBox.volume_layer_box <;> assumption)
