import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleTensorOfSemisimplePotentials
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.LiftApplyOfMemAdmissibleSubalgebra
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.Comp.ssbb_of_ssPotB` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSemisimpleTensorOfSemisimplePotentials.lean&line=36#L36)
-/
theorem _root_.GlobalTheory.T.semisimple_tensor_of_semisimple_potentials : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  first | exact @GlobalTheory.KZ.Comp.ssbb_of_ssPotB | exact GlobalTheory.KZ.Comp.ssbb_of_ssPotB | (intros; apply GlobalTheory.KZ.Comp.ssbb_of_ssPotB <;> assumption)
