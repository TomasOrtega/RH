import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMeromorphicRootOfMemModularFunctionTowerUn
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsMeromorphicRootOfMemModularFunctionTowerUn.lean&line=96#L96)
-/
theorem _root_.GlobalTheory.T.exists_meromorphic_root_of_mem_modularFunctionTower_Un : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ), 0 < m → ∀ f ∈ X.Un m, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ X.an (f : X.K) * (b : Mero) ^ m = (a : Mero) ^ m := by
  first | exact @GlobalTheory.KZ.MeroRoot.exists_mero_root | exact GlobalTheory.KZ.MeroRoot.exists_mero_root | (intros; apply GlobalTheory.KZ.MeroRoot.exists_mero_root <;> assumption)
