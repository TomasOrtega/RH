import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UpperLevelIsUnitaryStabiliserBothLattices
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UpperStab.upper_isUStab` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FUpperLevelIsUnitaryStabiliserBothLattices.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.upperLevel_isUnitaryStabiliser_both_lattices : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [MulAction U C] (M : TwoLevels E r U C) (c : C), ∀ β ∈ M.upper c, IsUStab (M.comp c).Gm (M.comp c).L' β ∧ IsUStab (M.comp c).Gm (M.comp c).Λ β := by
  first | exact @GlobalTheory.UpperStab.upper_isUStab | exact GlobalTheory.UpperStab.upper_isUStab | (intros; apply GlobalTheory.UpperStab.upper_isUStab <;> assumption)
