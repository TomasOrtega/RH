import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedGramReEqSq
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeFrameGram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModelHodgeGram
open Matrix
open scoped ComplexOrder
open GlobalTheory.HodgeLocGeo

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.GradedGramRe.gradedGram_re_eq_grSq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FGradedGramReEqSq.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.graded_gram_re_eq_sq : ∀ {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ), M.PosDef → ∀ i : Fin n, (GlobalTheory.HermFrame.gradedGram M i () ()).re = GlobalTheory.GradedNorm.grSq M i := by
  first | exact @GlobalTheory.GradedGramRe.gradedGram_re_eq_grSq | exact GlobalTheory.GradedGramRe.gradedGram_re_eq_grSq | (intros; apply GlobalTheory.GradedGramRe.gradedGram_re_eq_grSq <;> assumption)
