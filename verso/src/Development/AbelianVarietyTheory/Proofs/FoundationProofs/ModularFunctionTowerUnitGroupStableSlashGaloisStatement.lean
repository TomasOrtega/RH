import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionTowerUnitGroupStableSlashGalois
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.Tower.Un_sl_gal` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FModularFunctionTowerUnitGroupStableSlashGalois.lean&line=40#L40)
-/
theorem _root_.GlobalTheory.T.modularFunctionTower_unitGroup_stable_slash_galois : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (m : ℕ) (f : X.Kˣ), f ∈ X.Un m → (∀ (g : GQ) (u : X.Kˣ), (u : X.K) = X.sl g (f : X.K) → u ∈ X.Un m) ∧ ∀ (s : Ω ≃ₐ[ℚ] Ω) (u : X.Kˣ), (u : X.K) = X.gal s (f : X.K) → u ∈ X.Un m := by
  first | exact @GlobalTheory.KZ.Tower.Un_sl_gal | exact GlobalTheory.KZ.Tower.Un_sl_gal | (intros; apply GlobalTheory.KZ.Tower.Un_sl_gal <;> assumption)
