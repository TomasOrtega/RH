import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHaarRightInvariant
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FUnimodularHaarRightInvariant.lean&line=11#L11)
-/
theorem _root_.GlobalTheory.T.unimodular_haar_right_invariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | exact GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | (intros; apply GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod <;> assumption)
