import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WaveKernelUniqueness
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FWaveKernelUniqueness.lean&line=241#L241)
-/
theorem _root_.GlobalTheory.T.wave_kernel_uniqueness : PositivityTheory.RgBcC.KerUniq := by
  first | exact @GlobalTheory.CompanionTheory.KerUniq.main | exact GlobalTheory.CompanionTheory.KerUniq.main | (intros; apply GlobalTheory.CompanionTheory.KerUniq.main <;> assumption)
