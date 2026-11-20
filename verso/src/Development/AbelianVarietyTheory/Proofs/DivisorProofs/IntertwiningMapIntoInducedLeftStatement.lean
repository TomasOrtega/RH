import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwiningMapIntoInducedLeft
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ScaledIntegerPeriodic
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KSplitInd.mapA_mem_indSp` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntertwiningMapIntoInducedLeft.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.intertwining_map_into_induced_left : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a a' : ℕ) (α β : kˣ →* ℂˣ) (l : (Matrix (Fin a) (Fin a) k → ℂ) → ℂ), IsSmU β →
    IsEqv (α / β) (((a + a' : ℕ) : ℂ) / 2) l → ∀ Φ ∈ SB (Matrix (Fin a) (Fin (a + a')) k), mapA a' l (α / β) β Φ ∈ indSp a a' α β := by
  first | exact @GlobalTheory.KSplitInd.mapA_mem_indSp | exact GlobalTheory.KSplitInd.mapA_mem_indSp | (intros; apply GlobalTheory.KSplitInd.mapA_mem_indSp <;> assumption)
