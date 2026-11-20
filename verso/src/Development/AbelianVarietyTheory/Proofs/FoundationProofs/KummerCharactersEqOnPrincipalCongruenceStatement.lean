import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KummerCharactersEqOnPrincipalCongruence
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRootOne
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.H3.kum_near` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FKummerCharactersEqOnPrincipalCongruence.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.kummerCharacters_eqOn_principalCongruence : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], ∀ n : ℕ, ∀ (x : X.Khat l) (χ χ' : SL(2, ℤ) → ZMod (l ^ n)), Kum X l n x χ → Kum X l n x χ' → Near χ χ' := by
  first | exact @GlobalTheory.KZ.H3.kum_near | exact GlobalTheory.KZ.H3.kum_near | (intros; apply GlobalTheory.KZ.H3.kum_near <;> assumption)
