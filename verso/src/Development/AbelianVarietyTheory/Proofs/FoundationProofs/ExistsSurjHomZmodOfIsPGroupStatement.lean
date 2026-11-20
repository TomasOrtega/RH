import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSurjHomZmodOfIsPGroup
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsSurjHomZmodOfIsPGroup.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_surjective_hom_zmod_of_isPGroup : ∀ (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] [Nontrivial G], IsPGroup p G → ∃ χ : G →* Multiplicative (ZMod p), Function.Surjective χ := by
  first | exact @GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | exact GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup | (intros; apply GlobalTheory.AlmostEt.exists_surj_hom_zmod_of_isPGroup <;> assumption)
