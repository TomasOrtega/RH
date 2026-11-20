import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLevelBlockLevelsSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DgMatOne
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.CtLevel
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.BCT.CtLevel.isLevel_lev_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FIsLevelBlockLevelsSplitPlace.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.isLevel_blockLevels_splitPlace : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b n : ℕ) (h : a + b = n) (w : Pl E)
    (N : Subgroup (GLw n w)) (μ : (w.adicCompletion E)ˣ →* ℂˣ), IsSplitAt w → IsOpen (N : Set (GLw n w)) →
    IsOpen {x | μ x = 1} →
    IsLevel (thL a w) (GlobalTheory.LFun.KGL w a) (lev₁ h w N μ) ∧ IsLevel (thL b w) (GlobalTheory.LFun.KGL w b) (lev₂ h w N μ) := by
  first | exact @GlobalTheory.BCT.CtLevel.isLevel_lev_split | exact GlobalTheory.BCT.CtLevel.isLevel_lev_split | (intros; apply GlobalTheory.BCT.CtLevel.isLevel_lev_split <;> assumption)
