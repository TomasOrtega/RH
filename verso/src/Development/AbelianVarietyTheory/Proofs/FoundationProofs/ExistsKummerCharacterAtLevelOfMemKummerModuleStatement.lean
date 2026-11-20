import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsKummerCharacterAtLevelOfMemKummerModule
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.H3.exists_kum_of_mem_A` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsKummerCharacterAtLevelOfMemKummerModule.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.exists_kummerCharacterAtLevel_of_mem_kummerModule : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], JHol X → ∀ (n : ℕ), ∀ x ∈ X.A l, ∃ χ : SL(2, ℤ) → ZMod (l ^ n), Kum X l n x χ := by
  first | exact @GlobalTheory.KZ.H3.exists_kum_of_mem_A | exact GlobalTheory.KZ.H3.exists_kum_of_mem_A | (intros; apply GlobalTheory.KZ.H3.exists_kum_of_mem_A <;> assumption)
