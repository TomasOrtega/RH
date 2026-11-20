import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnimodularHaarRightInvariant
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | exact GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | (intros; apply GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.unimodular_haar_right_invariant : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G], IsUnimod G → ∀ (μ : Measure G) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | exact GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod | (intros; apply GlobalTheory.CompanionTheory.HaarUnimod.isMulRightInvariant_of_isUnimod <;> assumption)
