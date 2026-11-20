import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSlTwoInvariantHolomorphicMemAdjoinJInvariant.lean&line=71#L71)
-/
theorem _root_.GlobalTheory.T.slTwo_invariant_holomorphic_mem_adjoin_jInvariant : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) → h ∈ Algebra.adjoin Ω {X.jK} := by
  first | exact @GlobalTheory.KZ.LevelOne.mem_adjoin_j | exact GlobalTheory.KZ.LevelOne.mem_adjoin_j | (intros; apply GlobalTheory.KZ.LevelOne.mem_adjoin_j <;> assumption)
