import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsMulMemAddWeight
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemDomOfIsom
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn GlobalTheory.CuspEmb
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CuspEmb.twoLevels_mul_mem_SS` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwoLevelCuspFormsMulMemAddWeight.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.twoLevelCuspForms_mul_mem_add_weight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (la mu : Wt M.Ψ r) (F G : C → Frame M.Ψ r → ℂ), F ∈ M.SS la → G ∈ M.SS mu → F * G ∈ M.SS (la + mu) := by
  first | exact @GlobalTheory.CuspEmb.twoLevels_mul_mem_SS | exact GlobalTheory.CuspEmb.twoLevels_mul_mem_SS | (intros; apply GlobalTheory.CuspEmb.twoLevels_mul_mem_SS <;> assumption)
