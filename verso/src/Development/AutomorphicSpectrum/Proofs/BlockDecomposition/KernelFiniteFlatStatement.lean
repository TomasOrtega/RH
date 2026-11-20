import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFiniteFlat
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZarhinDualPolarisation.FlatFiniteFibres.FlatOfFibresFinite
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FKernelFiniteFlat.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.kernel_finite_flat : PositivityTheory.Tls2.Zar3.Ch1.KernelFinFlat := by
  first | exact @GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | exact GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat | (intros; apply GlobalTheory.CompanionTheory.Ar.KerFF.kernelFinFlat <;> assumption)
