import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsTotallyIsotropicFlagComplexifiedSaturatedFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FIsTotallyIsotropicFlagComplexifiedSaturatedFlag.lean&line=99#L99)
-/
theorem _root_.GlobalTheory.T.isTotallyIsotropicFlag_complexified_saturatedFlag : ∀ (I : AutInst) (Λ : Submodule (𝓞 I.E) (Fin I.n → I.E)) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I Λ j S → ∀ v, IsIsoFlag (I.ε v) j (flagAt I S v) := by
  first | exact @GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | exact GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag | (intros; apply GlobalTheory.FlagMeas.isIsoFlag_flagAt_of_isSatFlag <;> assumption)
