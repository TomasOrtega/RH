import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousRightPartialFourier
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Lpart
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData GlobalTheory.CompanionTheory.GL2DualWhittakerPair
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FContinuousRightPartialFourier.lean&line=17#L17)
-/
theorem _root_.GlobalTheory.T.continuous_right_partial_fourier : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ Φ ∈ LFS.SB F, ∀ h : GL (Fin 2) F, Continuous fun z : GL (Fin 2) F => Rpart ψ (Pf Φ h z) := by
  first | exact @GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont.continuous_Rpart_Pf | exact GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont.continuous_Rpart_Pf | (intros; apply GlobalTheory.CompanionTheory.GL2DualWhittakerPair.PfCont.continuous_Rpart_Pf <;> assumption)
