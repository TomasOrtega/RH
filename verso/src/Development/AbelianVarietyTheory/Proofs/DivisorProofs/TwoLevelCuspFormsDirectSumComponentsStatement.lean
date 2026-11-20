import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsDirectSumComponents
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTwoLevelCuspFormsDirectSumComponents.lean&line=134#L134)
-/
theorem _root_.GlobalTheory.T.twoLevelCuspForms_directSum_components : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C] [DecidableEq C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)), IsPullRep M ka ρ → ∃ A : C → Submodule ℂ (M.cusp ka), DirectSum.IsInternal A ∧ ∀ (h : U) (c : C), ∀ v ∈ A c, ρ h v ∈ A (h • c) := by
  first | exact @GlobalTheory.ShareOn.cusp_decomp | exact GlobalTheory.ShareOn.cusp_decomp | (intros; apply GlobalTheory.ShareOn.cusp_decomp <;> assumption)
