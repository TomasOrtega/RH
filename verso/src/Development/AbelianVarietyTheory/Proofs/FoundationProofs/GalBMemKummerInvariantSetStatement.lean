import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GalBMemKummerInvariantSet
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FGalBMemKummerInvariantSet.lean&line=127#L127)
-/
theorem _root_.GlobalTheory.T.galB_mem_kummer_invariant_set : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ (s : Ω ≃ₐ[ℚ] Ω), ∀ b ∈ X.B N l w, X.galB l s b ∈ X.B N l w := by
  first | exact @GlobalTheory.KZ.StabGal.galB_mem_B | exact GlobalTheory.KZ.StabGal.galB_mem_B | (intros; apply GlobalTheory.KZ.StabGal.galB_mem_B <;> assumption)
