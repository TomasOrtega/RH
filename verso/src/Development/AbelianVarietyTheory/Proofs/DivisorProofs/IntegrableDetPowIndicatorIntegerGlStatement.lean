import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableDetPowIndicatorIntegerGl
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegrableDetPowIndicatorIntegerGl.lean&line=14#L14)
-/
theorem _root_.GlobalTheory.T.integrable_det_pow_indicator_integer_gl : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (n : ℕ) (σ : ℝ), (n : ℝ) - 1 < σ →
    Integrable (fun g : GL (Fin n) k => (intM k (Fin n) (Fin n)).indicator (fun _ => (1 : ℝ)) g.val * nabs k (gdet g) ^ σ) (haarVol (KO k (Fin n))) := by
  first | exact @GlobalTheory.GJTransfer.integrable_indicator_intM_mul_nabs_rpow | exact GlobalTheory.GJTransfer.integrable_indicator_intM_mul_nabs_rpow | (intros; apply GlobalTheory.GJTransfer.integrable_indicator_intM_mul_nabs_rpow <;> assumption)
