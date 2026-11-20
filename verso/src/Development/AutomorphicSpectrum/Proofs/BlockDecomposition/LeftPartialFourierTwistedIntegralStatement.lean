import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftPartialFourierTwistedIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice.sliceForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FLeftPartialFourierTwistedIntegral.lean&line=89#L89)
-/
theorem _root_.GlobalTheory.T.left_partial_fourier_twisted_integral : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ p : Matrix (Fin 2) (Fin 2) F → ℂ, SB2 p → ∫ u, (ψ u : ℂ) * Lpart ψ (fun M => p ((uni2 (-u)).val * M)) ∂selfDualMeasure ψ = rr ψ p 1 := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice.sliceForm | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice.sliceForm | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.Slice.sliceForm <;> assumption)
