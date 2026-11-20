import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFormNonzeroAtOneLift
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCuspFormNonzeroAtOneLift.lean&line=75#L75)
-/
theorem _root_.GlobalTheory.T.exists_cuspForm_nonzero_at_one_lift : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite U] [Finite C] [MulAction U C] (M : TwoLevels E r U C), LevelHyp M → ∀ s : ℕ, Even s → 2 * r + 50 * r ^ 2 * M.dimX + 1 ≤ s → ∀ (c : C) (x : Frame M.Ψ r), GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.NoContraction (M.comp c) (castFrame (M.comp_Ψ c).symm x) → x ∈ M.dom → ∃ u ∈ M.SS (deMul M.Ψ r M.p0 s), u c x ≠ 0 ∧ (∀ h : U, h ≠ 1 → M.pull h u c x = 0) ∧ ∀ c', (∀ h : U, h • c ≠ c') → ∀ y, u c' y = 0 := by
  first | exact @GlobalTheory.LiftInterp.exists_form_one_lift | exact GlobalTheory.LiftInterp.exists_form_one_lift | (intros; apply GlobalTheory.LiftInterp.exists_form_one_lift <;> assumption)
