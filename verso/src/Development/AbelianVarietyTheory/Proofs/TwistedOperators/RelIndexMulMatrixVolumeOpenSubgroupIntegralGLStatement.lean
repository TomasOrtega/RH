import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelIndexMulMatrixVolumeOpenSubgroupIntegralGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BorelParam
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.IndexVolume.relIndex_mul_volM` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FRelIndexMulMatrixVolumeOpenSubgroupIntegralGL.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.relIndex_mul_matrixVolume_open_subgroup_integralGL : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure]
    (n : Type) [Fintype n] [DecidableEq n] (H L : Subgroup (GL n k)),
    H ≤ L → L ≤ KO k n → IsOpen (H : Set (GL n k)) →
    0 < (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal ∧
    (H.relIndex L : ℝ) * (volM ν n n (Units.val '' (H : Set (GL n k)))).toReal =
      (volM ν n n (Units.val '' (L : Set (GL n k)))).toReal := by
  first | exact @GlobalTheory.IndexVolume.relIndex_mul_volM | exact GlobalTheory.IndexVolume.relIndex_mul_volM | (intros; apply GlobalTheory.IndexVolume.relIndex_mul_volM <;> assumption)
