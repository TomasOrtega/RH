import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsIntegralModularTowerJCompGlTwoPosRat
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.JInt.jK_sl_isIntegral` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIsIntegralModularTowerJCompGlTwoPosRat.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.isIntegral_modularTower_j_comp_glTwoPosRat : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ g : GQ, IsIntegral (Algebra.adjoin Ω {X.jK}) (X.sl g X.jK) := by
  first | exact @GlobalTheory.KZ.JInt.jK_sl_isIntegral | exact GlobalTheory.KZ.JInt.jK_sl_isIntegral | (intros; apply GlobalTheory.KZ.JInt.jK_sl_isIntegral <;> assumption)
