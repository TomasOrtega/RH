import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerClassEvalEqZeroOfVanishingOnCongruence
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.H3.kum_near_zero_eval` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKummerClassEvalEqZeroOfVanishingOnCongruence.lean&line=62#L62)
-/
theorem _root_.GlobalTheory.T.kummerClass_eval_eq_zero_of_vanishing_on_congruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Near χ 0 → AdicCompletion.eval (idl l) (X.Kl l) n x = 0 := by
  first | exact @GlobalTheory.KZ.H3.kum_near_zero_eval | exact GlobalTheory.KZ.H3.kum_near_zero_eval | (intros; apply GlobalTheory.KZ.H3.kum_near_zero_eval <;> assumption)
