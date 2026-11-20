import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBettiCocycleKummerRelation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsBettiCocycleKummerRelation.lean&line=31#L31)
-/
theorem _root_.GlobalTheory.T.exists_betti_cocycle_kummer_relation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  first | exact @GlobalTheory.KZ.BettiEx.exists_betti_cocycle | exact GlobalTheory.KZ.BettiEx.exists_betti_cocycle | (intros; apply GlobalTheory.KZ.BettiEx.exists_betti_cocycle <;> assumption)
