import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitMinorStableIntegralGroup
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
open MeasureTheory GlobalTheory.SplitFlip ValuativeRel
open scoped Matrix
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUnitMinorStableIntegralGroup.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.unit_minor_stable_integral_group : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (E : GL (Fin n) k) (Y : Matrix (Fin n) (Fin d) k), E ∈ GlobalTheory.SplitWeil.KO k (Fin n) →
    Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d → E.val * Y ∈ GlobalTheory.FullRankCoinv.UnitMinor.unitMinorSet k n d := by
  first | exact @GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet | exact GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet | (intros; apply GlobalTheory.UnitMinorStable.mul_mem_unitMinorSet <;> assumption)
