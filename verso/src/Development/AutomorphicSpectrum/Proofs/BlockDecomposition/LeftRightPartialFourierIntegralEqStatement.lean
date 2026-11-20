import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftRightPartialFourierIntegralEq
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeftRightPartialFourierIntegralEq.lean&line=65#L65)
-/
theorem _root_.GlobalTheory.T.left_right_partial_fourier_integral_eq : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → (∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ = ∫ t, (ψ t : ℂ) * Rpart ψ (fun M => p ((uni2 (-t)).val * M)) ∂selfDualMeasure ψ) → ∀ (A : GL (Fin 2) F → ℂ) (P : GL (Fin 2) F → Matrix (Fin 2) (Fin 2) F → ℂ), (∀ u z, A (uni2 u * z) = (ψ u : ℂ) * A z) → (∀ u z M, P (uni2 u * z) M = P z ((uni2 (-u)).val * M)) → (∀ z, SB2 (P z)) → Integrable (fun z => A z * Lpart ψ (P z)) (LFS.hG ψ) → Integrable (fun z => A z * Rpart ψ (P z)) (LFS.hG ψ) → ∫ z, A z * Lpart ψ (P z) ∂LFS.hG ψ = ∫ z, A z * Rpart ψ (P z) ∂LFS.hG ψ := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.CellFubini.core | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.CellFubini.core | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.CellFubini.core <;> assumption)
