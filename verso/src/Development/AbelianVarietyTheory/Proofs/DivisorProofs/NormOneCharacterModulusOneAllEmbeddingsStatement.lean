import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneCharacterModulusOneAllEmbeddings
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetRefinement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNormOneCharacterModulusOneAllEmbeddings.lean&line=126#L126)
-/
theorem _root_.GlobalTheory.T.normOneCharacter_modulusOne_all_embeddings : ∀ (D : D7) (χ : TaylorLogMetric.IdE D → ℂ), TaylorLogMetric.IsChi D χ → ∀ 𝔞 : TaylorLogMetric.IdE D, TaylorLogMetric.N1 D 𝔞 → StandardLatticesGL3.Mod1All (χ 𝔞) := by
  first | exact @GlobalTheory.CharModOne.mod1All_of_isChi | exact GlobalTheory.CharModOne.mod1All_of_isChi | (intros; apply GlobalTheory.CharModOne.mod1All_of_isChi <;> assumption)
