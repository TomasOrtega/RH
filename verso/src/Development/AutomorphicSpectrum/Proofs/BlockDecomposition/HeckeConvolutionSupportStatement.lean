import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeConvolutionSupport
import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FHeckeConvolutionSupport.lean&line=12#L12)
-/
theorem _root_.GlobalTheory.T.hecke_convolution_support : ∀ (H : Type) [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H] (K L : Subgroup H) (f₁ f₂ : H → ℂ), L ≤ K → L.relIndex K ≠ 0 → IsHecke L f₁ → IsHecke L f₂ →
  IsHecke L (fun y => hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ∧ ∀ y, (hint K fun z => f₁ z * f₂ (z⁻¹ * y)) ≠ 0 → ∃ z, f₁ z ≠ 0 ∧ f₂ (z⁻¹ * y) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke | exact GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke | (intros; apply GlobalTheory.CompanionTheory.ConvHecke.conv_isHecke <;> assumption)
