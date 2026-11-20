import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
open NumberField GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.WachBlock.integralBlock_of_blockPair` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIntegralCrystallineBlockDataOfReductionPair.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.integralCrystallineBlockData_of_reductionPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  first | exact @GlobalTheory.WachBlock.integralBlock_of_blockPair | exact GlobalTheory.WachBlock.integralBlock_of_blockPair | (intros; apply GlobalTheory.WachBlock.integralBlock_of_blockPair <;> assumption)
