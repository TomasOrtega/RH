import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EqZeroOfBettiKummerRelationPadicZero
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FEqZeroOfBettiKummerRelationPadicZero.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.eq_zero_of_bettiKummerRelationPadic_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l : ℕ) [Fact l.Prime], 0 < N → ∀ b : X.Fn l, BtZ X N l b 0 → b = 0 := by
  first | exact @GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero | exact GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero | (intros; apply GlobalTheory.KZ.BettiB.eq_zero_of_btZ_zero <;> assumption)
