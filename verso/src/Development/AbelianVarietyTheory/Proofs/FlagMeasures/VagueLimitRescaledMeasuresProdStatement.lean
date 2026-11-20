import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.VagueLimitRescaledMeasuresProd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FVagueLimitRescaledMeasuresProd.lean&line=166#L166)
-/
theorem _root_.GlobalTheory.T.vague_limit_rescaled_measures_prod : ∀ (α β V W : Type) [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (c : α → V) (c' : β → W) (lam : Measure V) (lam' : Measure W) [IsLocallyFiniteMeasure lam] [IsLocallyFiniteMeasure lam'] (d d' : ℕ), Measurable c → Measurable c' → Vag μ c lam d → Vag ν c' lam' d' → Vag (μ.prod ν) (Prod.map c c') (lam.prod lam') (d + d') := by
  first | exact @GlobalTheory.IwConst.vag_prod | exact GlobalTheory.IwConst.vag_prod | (intros; apply GlobalTheory.IwConst.vag_prod <;> assumption)
